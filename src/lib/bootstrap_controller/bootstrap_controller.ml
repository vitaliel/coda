open Core
open Async
open Coda_base
open Coda_state
open Pipe_lib.Strict_pipe
open Coda_transition

module type Inputs_intf = sig
  module Transition_frontier : module type of Transition_frontier

  module Root_sync_ledger :
    Syncable_ledger.S
    with type addr := Ledger.Location.Addr.t
     and type hash := Ledger_hash.t
     and type root_hash := Ledger_hash.t
     and type merkle_tree := Ledger.Db.t
     and type account := Account.t
     and type merkle_path := Ledger.path
     and type query := Sync_ledger.Query.t
     and type answer := Sync_ledger.Answer.t

  module Network : Coda_intf.Network_intf

  module Sync_handler :
    Coda_intf.Sync_handler_intf
    with type transition_frontier := Transition_frontier.t
end

module Make (Inputs : Inputs_intf) : sig
  open Inputs

  include
    Coda_intf.Bootstrap_controller_intf
    with type network := Network.t
     and type transition_frontier := Transition_frontier.t
     and type persistent_root := Transition_frontier.Persistent_root.t
     and type persistent_frontier := Transition_frontier.Persistent_frontier.t

  module For_tests : sig
    type t

    val make_bootstrap :
         logger:Logger.t
      -> trust_system:Trust_system.t
      -> verifier:Verifier.t
      -> genesis_root:External_transition.Validated.t
      -> network:Network.t
      -> t

    val on_transition :
         t
      -> sender:Unix.Inet_addr.t
      -> root_sync_ledger:( State_hash.t
                          * Unix.Inet_addr.t
                          * Staged_ledger_hash.t )
                          Root_sync_ledger.t
      -> External_transition.t
      -> [> `Syncing_new_snarked_ledger | `Updating_root_transition | `Ignored]
         Deferred.t

    val run :
         logger:Logger.t
      -> trust_system:Trust_system.t
      -> verifier:Verifier.t
      -> network:Network.t
      -> consensus_local_state:Consensus.Data.Local_state.t
      -> transition_reader:( [< `Transition of
                                External_transition.Initial_validated.t
                                Envelope.Incoming.t ]
                           * [< `Time_received of Block_time.t] )
                           Pipe_lib.Strict_pipe.Reader.t
      -> should_ask_best_tip:bool
      -> persistent_root:Transition_frontier.Persistent_root.t
      -> persistent_frontier:Transition_frontier.Persistent_frontier.t
      -> initial_root_transition:External_transition.Validated.t
      -> ( Transition_frontier.t
         * External_transition.Initial_validated.t Envelope.Incoming.t list )
         Deferred.t

    val sync_ledger :
         t
      -> root_sync_ledger:( State_hash.t
                          * Unix.Inet_addr.t
                          * Staged_ledger_hash.t )
                          Root_sync_ledger.t
      -> transition_graph:Transition_cache.t
      -> sync_ledger_reader:( [< `Transition of
                                 External_transition.Initial_validated.t
                                 Envelope.Incoming.t ]
                            * [< `Time_received of 'a] )
                            Pipe_lib.Strict_pipe.Reader.t
      -> unit Deferred.t
  end
end = struct
  open Inputs

  type t =
    { logger: Logger.t
    ; trust_system: Trust_system.t
    ; verifier: Verifier.t
    ; mutable best_seen_transition: External_transition.Initial_validated.t
    ; mutable current_root: External_transition.Initial_validated.t
    ; network: Network.t }

  let worth_getting_root t candidate =
    `Take
    = Consensus.Hooks.select
        ~logger:
          (Logger.extend t.logger
             [ ( "selection_context"
               , `String "Bootstrap_controller.worth_getting_root" ) ])
        ~existing:
          ( t.best_seen_transition
          |> External_transition.Initial_validated.consensus_state )
        ~candidate

  let received_bad_proof t sender_host e =
    Trust_system.(
      record t.trust_system t.logger sender_host
        Actions.
          ( Violated_protocol
          , Some
              ( "Bad ancestor proof: $error"
              , [("error", `String (Error.to_string_hum e))] ) ))

  let done_syncing_root root_sync_ledger =
    Option.is_some (Root_sync_ledger.peek_valid_tree root_sync_ledger)

  let should_sync ~root_sync_ledger t candidate_state =
    (not @@ done_syncing_root root_sync_ledger)
    && worth_getting_root t candidate_state

  let start_sync_job_with_peer ~sender ~root_sync_ledger t peer_best_tip
      peer_root =
    let%bind () =
      Trust_system.(
        record t.trust_system t.logger sender
          Actions.
            ( Fulfilled_request
            , Some ("Received verified peer root and best tip", []) ))
    in
    t.best_seen_transition <- peer_best_tip ;
    t.current_root <- peer_root ;
    let blockchain_state =
      t.current_root |> External_transition.Initial_validated.blockchain_state
    in
    let expected_staged_ledger_hash =
      blockchain_state |> Blockchain_state.staged_ledger_hash
    in
    let snarked_ledger_hash =
      blockchain_state |> Blockchain_state.snarked_ledger_hash
    in
    return
    @@
    match
      Root_sync_ledger.new_goal root_sync_ledger
        (Frozen_ledger_hash.to_ledger_hash snarked_ledger_hash)
        ~data:
          ( External_transition.Initial_validated.state_hash t.current_root
          , sender
          , expected_staged_ledger_hash )
        ~equal:(fun (hash1, _, _) (hash2, _, _) -> State_hash.equal hash1 hash2)
    with
    | `New ->
        `Syncing_new_snarked_ledger
    | `Update_data ->
        `Updating_root_transition
    | `Repeat ->
        `Ignored

  let on_transition t ~sender ~root_sync_ledger
      (candidate_transition : External_transition.t) =
    let candidate_state =
      External_transition.consensus_state candidate_transition
    in
    if not @@ should_sync ~root_sync_ledger t candidate_state then
      Deferred.return `Ignored
    else
      match%bind Network.get_ancestry t.network sender candidate_state with
      | Error e ->
          Deferred.return
          @@ Fn.const `Ignored
          @@ Logger.error t.logger ~module_:__MODULE__ ~location:__LOC__
               ~metadata:[("error", `String (Error.to_string_hum e))]
               !"Could not get the proof of the root transition from the \
                 network: $error"
      | Ok peer_root_with_proof -> (
          match%bind
            Sync_handler.Root.verify ~logger:t.logger ~verifier:t.verifier
              candidate_state peer_root_with_proof
          with
          | Ok (`Root root, `Best_tip best_tip) ->
              if done_syncing_root root_sync_ledger then return `Ignored
              else
                start_sync_job_with_peer ~sender ~root_sync_ledger t best_tip
                  root
          | Error e ->
              return (received_bad_proof t sender e |> Fn.const `Ignored) )

  let sync_ledger t ~root_sync_ledger ~transition_graph ~sync_ledger_reader =
    let query_reader = Root_sync_ledger.query_reader root_sync_ledger in
    let response_writer = Root_sync_ledger.answer_writer root_sync_ledger in
    Network.glue_sync_ledger t.network query_reader response_writer ;
    Reader.iter sync_ledger_reader
      ~f:(fun (`Transition incoming_transition, `Time_received _) ->
        let ({With_hash.data= transition; hash}, _)
              : External_transition.Initial_validated.t =
          Envelope.Incoming.data incoming_transition
        in
        let previous_state_hash = External_transition.parent_hash transition in
        let sender =
          match Envelope.Incoming.sender incoming_transition with
          | Envelope.Sender.Local ->
              failwith
                "Unexpected, we should be syncing only to remote nodes in \
                 sync ledger"
          | Envelope.Sender.Remote inet_addr ->
              inet_addr
        in
        Transition_cache.add transition_graph ~parent:previous_state_hash
          incoming_transition ;
        (* TODO: Efficiently limiting the number of green threads in #1337 *)
        if
          worth_getting_root t (External_transition.consensus_state transition)
        then (
          Logger.trace t.logger
            !"Added the transition from sync_ledger_reader into cache"
            ~location:__LOC__ ~module_:__MODULE__
            ~metadata:
              [ ("state_hash", State_hash.to_yojson hash)
              ; ( "external_transition"
                , External_transition.to_yojson transition ) ] ;
          Deferred.ignore
          @@ on_transition t ~sender ~root_sync_ledger transition )
        else Deferred.unit )

  let download_best_tip ~root_sync_ledger ~transition_graph t
      ({With_hash.data= initial_root_transition; _}, _) =
    let num_peers = 8 in
    let peers = Network.random_peers t.network num_peers in
    Logger.info t.logger
      "Requesting peers for their best tip to eagerly start bootstrap"
      ~module_:__MODULE__ ~location:__LOC__ ;
    Logger.info t.logger
      !"Number of peers that we are sampling: %i"
      (List.length peers) ~module_:__MODULE__ ~location:__LOC__ ;
    Deferred.List.iter peers ~f:(fun peer ->
        let initial_consensus_state =
          External_transition.consensus_state initial_root_transition
        in
        match%bind
          Network.get_bootstrappable_best_tip t.network peer
            initial_consensus_state
        with
        | Error e ->
            Logger.debug t.logger
              !"Could not get bootstrappable best tip from peer: \
                %{sexp:Error.t}"
              ~metadata:[("peer", Network_peer.Peer.to_yojson peer)]
              e ~location:__LOC__ ~module_:__MODULE__ ;
            Deferred.unit
        | Ok peer_best_tip -> (
            match%bind
              Sync_handler.Bootstrappable_best_tip.verify ~logger:t.logger
                ~verifier:t.verifier initial_consensus_state peer_best_tip
            with
            | Ok
                ( `Root root_with_validation
                , `Best_tip
                    ((best_tip_with_hash, _) as best_tip_with_validation) ) ->
                let best_tip = With_hash.data best_tip_with_hash in
                let logger =
                  Logger.extend t.logger
                    [ ("peer", Network_peer.Peer.to_yojson peer)
                    ; ("best tip", External_transition.to_yojson @@ best_tip)
                    ; ( "hash"
                      , State_hash.to_yojson
                        @@ With_hash.hash best_tip_with_hash ) ]
                in
                Transition_cache.add transition_graph
                  ~parent:(External_transition.parent_hash best_tip)
                  {data= best_tip_with_validation; sender= Remote peer.host} ;
                if
                  should_sync ~root_sync_ledger t
                  @@ External_transition.consensus_state best_tip
                then (
                  Logger.debug logger
                    "Syncing with peer's bootstrappable best tip"
                    ~module_:__MODULE__ ~location:__LOC__ ;
                  (* TODO: Efficiently limiting the number of green threads in #1337 *)
                  Deferred.ignore
                    (start_sync_job_with_peer ~sender:peer.host
                       ~root_sync_ledger t best_tip_with_validation
                       root_with_validation) )
                else (
                  Logger.debug logger
                    !"Will not sync with peer's bootstrappable best tip "
                    ~location:__LOC__ ~module_:__MODULE__ ;
                  Deferred.unit )
            | Error e ->
                let error_msg =
                  sprintf
                    !"Peer %{sexp:Network_peer.Peer.t} sent us bad proof for \
                      their best tip"
                    peer
                in
                Logger.warn t.logger !"%s" error_msg ~module_:__MODULE__
                  ~location:__LOC__
                  ~metadata:[("error", `String (Error.to_string_hum e))] ;
                ignore
                  Trust_system.(
                    record t.trust_system t.logger peer.host
                      Actions.(Violated_protocol, Some (error_msg, []))) ;
                Deferred.unit ) )

  (* We conditionally ask other peers for their best tip. This is for testing
     eager bootstrapping and the regular functionalities of bootstrapping in
     isolation *)
  let run ~logger ~trust_system ~verifier ~network ~consensus_local_state
      ~transition_reader ~should_ask_best_tip ~persistent_root
      ~persistent_frontier ~initial_root_transition =
    let id = ref 0 in
    let log_mask ctx =
      Ledger.Maskable.Debug.visualize
        ~filename:(Printf.sprintf "bootstrap.%d.%s.dot" !id ctx) ;
      incr id
    in
    log_mask "genesis" ;
    let rec loop () =
      log_mask "start" ;
      let sync_ledger_reader, sync_ledger_writer =
        create ~name:"sync ledger pipe"
          (Buffered (`Capacity 50, `Overflow Crash))
      in
      don't_wait_for
        (transfer_while_writer_alive transition_reader sync_ledger_writer
           ~f:Fn.id) ;
      let initial_root_transition =
        initial_root_transition
        |> External_transition.Validation
           .reset_frontier_dependencies_validation
        |> External_transition.Validation.reset_staged_ledger_diff_validation
      in
      let t =
        { network
        ; logger
        ; trust_system
        ; verifier
        ; best_seen_transition= initial_root_transition
        ; current_root= initial_root_transition }
      in
      let transition_graph = Transition_cache.create () in
      let temp_persistent_root_instance =
        Transition_frontier.Persistent_root.create_instance_exn persistent_root
      in
      let temp_snarked_ledger =
        Transition_frontier.Persistent_root.Instance.snarked_ledger
          temp_persistent_root_instance
      in
      let%bind hash, sender, expected_staged_ledger_hash =
        let root_sync_ledger =
          Root_sync_ledger.create temp_snarked_ledger ~logger:t.logger
            ~trust_system
        in
        let%bind () =
          if should_ask_best_tip then
            download_best_tip ~root_sync_ledger ~transition_graph t
              initial_root_transition
          else Deferred.unit
        in
        don't_wait_for
          (sync_ledger t ~root_sync_ledger ~transition_graph
             ~sync_ledger_reader) ;
        (* We ignore the resulting ledger returned here since it will always
         * be the same as the ledger we started with because we are syncing
         * a db ledger. *)
        let%map _, data = Root_sync_ledger.valid_tree root_sync_ledger in
        Root_sync_ledger.destroy root_sync_ledger ;
        data
      in
      log_mask "sync" ;
      let%bind staged_ledger_aux_result =
        let open Deferred.Or_error.Let_syntax in
        let%bind scan_state, expected_merkle_root, pending_coinbases =
          Network.get_staged_ledger_aux_and_pending_coinbases_at_hash t.network
            sender hash
        in
        let received_staged_ledger_hash =
          Staged_ledger_hash.of_aux_ledger_and_coinbase_hash
            (Staged_ledger.Scan_state.hash scan_state)
            expected_merkle_root pending_coinbases
        in
        Logger.debug logger ~module_:__MODULE__ ~location:__LOC__
          ~metadata:
            [ ( "expected_staged_ledger_hash"
              , Staged_ledger_hash.to_yojson expected_staged_ledger_hash )
            ; ( "received_staged_ledger_hash"
              , Staged_ledger_hash.to_yojson received_staged_ledger_hash ) ]
          "Comparing $expected_staged_ledger_hash to \
           $received_staged_ledger_hash" ;
        let%bind () =
          Staged_ledger_hash.equal expected_staged_ledger_hash
            received_staged_ledger_hash
          |> Result.ok_if_true
               ~error:(Error.of_string "received faulty scan state from peer")
          |> Deferred.return
        in
        (* Construct the staged ledger before constructing the transition
         * frontier in order to verify the scan state we received.
         * TODO: reorganize the code to avoid doing this twice (#3480)  *)
        let%map _ =
          let open Deferred.Let_syntax in
          let temp_mask = Ledger.of_database temp_snarked_ledger in
          let%map result =
            Staged_ledger.of_scan_state_pending_coinbases_and_snarked_ledger
              ~logger ~verifier ~scan_state ~snarked_ledger:temp_mask
              ~expected_merkle_root ~pending_coinbases
          in
          ignore
            (Ledger.Maskable.unregister_mask_exn
               (Ledger.Mask.Attached.get_parent temp_mask)
               temp_mask) ;
          result
        in
        (scan_state, pending_coinbases)
      in
      Transition_frontier.Persistent_root.Instance.destroy
        temp_persistent_root_instance ;
      match staged_ledger_aux_result with
      | Error e ->
          log_mask "error" ;
          let%bind () =
            Trust_system.(
              record t.trust_system t.logger sender
                Actions.
                  ( Violated_protocol
                  , Some
                      ( "Can't find scan state from the peer or received \
                         faulty scan state from the peer."
                      , [] ) ))
          in
          Logger.error logger ~module_:__MODULE__ ~location:__LOC__
            ~metadata:
              [ ("error", `String (Error.to_string_hum e))
              ; ("state_hash", State_hash.to_yojson hash)
              ; ( "expected_staged_ledger_hash"
                , Staged_ledger_hash.to_yojson expected_staged_ledger_hash ) ]
            "Failed to find scan state for the transition with hash \
             $state_hash from the peer or received faulty scan state: $error. \
             Retry bootstrap" ;
          Writer.close sync_ledger_writer ;
          loop ()
      | Ok (scan_state, pending_coinbase) -> (
          log_mask "success" ;
          let%bind () =
            Trust_system.(
              record t.trust_system t.logger sender
                Actions.
                  ( Fulfilled_request
                  , Some ("Received valid scan state from peer", []) ))
          in
          let new_root =
            let root_transition =
              External_transition.Validation.forget_validation t.current_root
            in
            (* TODO: review the correctness of this action #2480 *)
            let (`I_swear_this_is_safe_see_my_comment
                  validated_root_transition) =
              External_transition.Validated.create_unsafe root_transition
            in
            validated_root_transition
          in
          let consensus_state =
            new_root |> External_transition.Validated.consensus_state
          in
          (* Synchronize consensus local state if necessary *)
          match%bind
            match
              Consensus.Hooks.required_local_state_sync ~consensus_state
                ~local_state:consensus_local_state
            with
            | None ->
                Logger.debug logger ~module_:__MODULE__ ~location:__LOC__
                  ~metadata:
                    [ ( "local_state"
                      , Consensus.Data.Local_state.to_yojson
                          consensus_local_state )
                    ; ( "consensus_state"
                      , Consensus.Data.Consensus_state.Value.to_yojson
                          consensus_state ) ]
                  "Not synchronizing consensus local state" ;
                Deferred.return @@ Ok ()
            | Some sync_jobs ->
                Logger.info logger ~module_:__MODULE__ ~location:__LOC__
                  "Synchronizing consensus local state" ;
                Consensus.Hooks.sync_local_state
                  ~local_state:consensus_local_state ~logger ~trust_system
                  ~random_peers:(fun n ->
                    List.append
                      (Network.peers_by_ip t.network sender)
                      (Network.random_peers t.network n) )
                  ~query_peer:
                    { Network_peer.query=
                        (fun peer f query ->
                          Network.query_peer t.network peer f query ) }
                  sync_jobs
          with
          | Error e ->
              log_mask "local_sync_error" ;
              Logger.error logger ~module_:__MODULE__ ~location:__LOC__
                ~metadata:[("error", `String (Error.to_string_hum e))]
                "Local state sync failed: $error. Retry bootstrap" ;
              Writer.close sync_ledger_writer ;
              loop ()
          | Ok () ->
              log_mask "local_sync_success" ;
              (* Close the old frontier and reload a new on from disk. *)
              let new_root_data =
                Transition_frontier.Root_data.Limited.Stable.V1.
                  {transition= new_root; scan_state; pending_coinbase}
              in
              let%bind () =
                Transition_frontier.Persistent_frontier.reset_database_exn
                  persistent_frontier ~root_data:new_root_data
              in
              (* TODO: lazy load db in persistent root to avoid unecessary opens like this *)
              Transition_frontier.Persistent_root.(
                with_instance_exn persistent_root ~f:(fun instance ->
                    Instance.set_root_state_hash instance
                      (External_transition.Validated.state_hash new_root) )) ;
              let%map new_frontier =
                let fail msg =
                  failwith
                    ( "failed to initialize transition frontier after \
                       bootstrapping: " ^ msg )
                in
                Transition_frontier.load
                  { Transition_frontier.logger= t.logger
                  ; verifier
                  ; consensus_local_state }
                  ~persistent_root ~persistent_frontier
                >>| function
                | Ok frontier ->
                    frontier
                | Error (`Failure msg) ->
                    fail msg
                | Error `Bootstrap_required ->
                    fail
                      "bootstrap still required (indicates logical error in \
                       code)"
                | Error `Persistent_frontier_malformed ->
                    fail "persistent frontier was malformed"
              in
              log_mask "load" ;
              Logger.info logger ~module_:__MODULE__ ~location:__LOC__
                "Bootstrap state: complete." ;
              let collected_transitions =
                Transition_cache.data transition_graph
              in
              let logger =
                Logger.extend logger
                  [ ( "context"
                    , `String "Filter collected transitions in bootstrap" ) ]
              in
              let root_consensus_state =
                Transition_frontier.(
                  Breadcrumb.consensus_state (root new_frontier))
              in
              let filtered_collected_transitions =
                List.filter collected_transitions
                  ~f:(fun incoming_transition ->
                    let With_hash.{data= transition; _}, _ =
                      Envelope.Incoming.data incoming_transition
                    in
                    `Take
                    = Consensus.Hooks.select ~existing:root_consensus_state
                        ~candidate:
                          (External_transition.consensus_state transition)
                        ~logger )
              in
              Logger.debug logger
                "Sorting filtered transitions by consensus state" ~metadata:[]
                ~location:__LOC__ ~module_:__MODULE__ ;
              let sorted_filtered_collected_transitins =
                List.sort filtered_collected_transitions
                  ~compare:
                    (Comparable.lift
                       ~f:(fun incoming_transition ->
                         let With_hash.{data= transition; _}, _ =
                           Envelope.Incoming.data incoming_transition
                         in
                         transition )
                       External_transition.compare)
              in
              (new_frontier, sorted_filtered_collected_transitins) )
    in
    let start_time = Core.Time.now () in
    let%map result = loop () in
    Coda_metrics.(
      Gauge.set Bootstrap.bootstrap_time_ms
        Core.Time.(Span.to_ms @@ diff (now ()) start_time)) ;
    result

  module For_tests = struct
    type nonrec t = t

    let make_bootstrap ~logger ~trust_system ~verifier ~genesis_root ~network =
      let transition =
        genesis_root
        |> External_transition.Validation
           .reset_frontier_dependencies_validation
        |> External_transition.Validation.reset_staged_ledger_diff_validation
      in
      { logger
      ; trust_system
      ; verifier
      ; best_seen_transition= transition
      ; current_root= transition
      ; network }

    let on_transition = on_transition

    module Transition_cache = Transition_cache

    let sync_ledger = sync_ledger

    let run = run
  end

  let run = run ~should_ask_best_tip:true
end

include Make (struct
  module Transition_frontier = Transition_frontier
  module Root_sync_ledger = Sync_ledger.Db
  module Network = Coda_networking
  module Sync_handler = Sync_handler
end)
