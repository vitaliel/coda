open Core
open Async
open Pipe_lib
open Coda_base
open Coda_state
open Coda_transition
open Signature_lib
open O1trace
open Otp_lib
module Time = Coda_base.Block_time

module Singleton_supervisor : sig
  type ('data, 'a) t

  val create :
    task:(unit Ivar.t -> 'data -> ('a, unit) Interruptible.t) -> ('data, 'a) t

  val cancel : (_, _) t -> unit

  val dispatch : ('data, 'a) t -> 'data -> ('a, unit) Interruptible.t
end = struct
  type ('data, 'a) t =
    { mutable task: (unit Ivar.t * ('a, unit) Interruptible.t) option
    ; f: unit Ivar.t -> 'data -> ('a, unit) Interruptible.t }

  let create ~task = {task= None; f= task}

  let cancel t =
    match t.task with
    | Some (ivar, _) ->
        Ivar.fill ivar () ;
        t.task <- None
    | None ->
        ()

  let dispatch t data =
    cancel t ;
    let ivar = Ivar.create () in
    let interruptible =
      let open Interruptible.Let_syntax in
      t.f ivar data
      >>| fun x ->
      t.task <- None ;
      x
    in
    t.task <- Some (ivar, interruptible) ;
    interruptible
end

module Transition_frontier_validation =
  External_transition.Transition_frontier_validation (Transition_frontier)

let time_to_ms = Fn.compose Time.Span.to_ms Time.to_span_since_epoch

let time_of_ms = Fn.compose Time.of_span_since_epoch Time.Span.of_ms

let lift_sync f =
  Interruptible.uninterruptible
    (Deferred.create (fun ivar -> Ivar.fill ivar (f ())))

module Singleton_scheduler : sig
  type t

  val create : Time.Controller.t -> t

  (** If you reschedule when already scheduled, take the min of the two schedulings *)
  val schedule : t -> Time.t -> f:(unit -> unit) -> unit
end = struct
  type t =
    { mutable timeout: unit Time.Timeout.t option
    ; time_controller: Time.Controller.t }

  let create time_controller = {time_controller; timeout= None}

  let cancel t =
    match t.timeout with
    | Some timeout ->
        Time.Timeout.cancel t.time_controller timeout () ;
        t.timeout <- None
    | None ->
        ()

  let schedule t time ~f =
    let remaining_time = Option.map t.timeout ~f:Time.Timeout.remaining_time in
    cancel t ;
    let span_till_time = Time.diff time (Time.now t.time_controller) in
    let wait_span =
      match remaining_time with
      | Some remaining when Time.Span.(remaining > Time.Span.of_ms Int64.zero)
        ->
          let min a b = if Time.Span.(a < b) then a else b in
          min remaining span_till_time
      | None | Some _ ->
          span_till_time
    in
    let timeout =
      Time.Timeout.create t.time_controller wait_span ~f:(fun _ ->
          t.timeout <- None ;
          f () )
    in
    t.timeout <- Some timeout
end

let generate_next_state ~previous_protocol_state ~time_controller
    ~staged_ledger ~transactions ~get_completed_work ~logger
    ~(keypair : Keypair.t) ~proposal_data ~scheduled_time =
  let open Interruptible.Let_syntax in
  let self = Public_key.compress keypair.public_key in
  let protocol_state_body_hash =
    Protocol_state.body previous_protocol_state |> Protocol_state.Body.hash
  in
  let%bind res =
    Interruptible.uninterruptible
      (let open Deferred.Let_syntax in
      let diff =
        measure "create_diff" (fun () ->
            Staged_ledger.create_diff staged_ledger ~self ~logger
              ~transactions_by_fee:transactions ~get_completed_work )
      in
      match%map
        Staged_ledger.apply_diff_unchecked staged_ledger diff
          protocol_state_body_hash
      with
      | Ok
          ( `Hash_after_applying next_staged_ledger_hash
          , `Ledger_proof ledger_proof_opt
          , `Staged_ledger transitioned_staged_ledger
          , `Pending_coinbase_data (is_new_stack, coinbase_amount) ) ->
          (*staged_ledger remains unchanged and transitioned_staged_ledger is discarded because the external transtion created out of this diff will be applied in Transition_frontier*)
          ignore
          @@ Ledger.unregister_mask_exn
               (Staged_ledger.ledger staged_ledger)
               (Staged_ledger.ledger transitioned_staged_ledger) ;
          Some
            ( diff
            , next_staged_ledger_hash
            , ledger_proof_opt
            , is_new_stack
            , coinbase_amount )
      | Error (Staged_ledger.Staged_ledger_error.Unexpected e) ->
          raise (Error.to_exn e)
      | Error e ->
          Logger.error logger ~module_:__MODULE__ ~location:__LOC__
            ~metadata:
              [ ( "error"
                , `String (Staged_ledger.Staged_ledger_error.to_string e) )
              ; ( "diff"
                , Staged_ledger_diff.With_valid_signatures_and_proofs.to_yojson
                    diff ) ]
            "Error applying the diff $diff: $error" ;
          None)
  in
  match res with
  | None ->
      Interruptible.return None
  | Some
      ( diff
      , next_staged_ledger_hash
      , ledger_proof_opt
      , is_new_stack
      , coinbase_amount ) ->
      let%bind protocol_state, consensus_transition_data =
        lift_sync (fun () ->
            let previous_ledger_hash =
              previous_protocol_state |> Protocol_state.blockchain_state
              |> Blockchain_state.snarked_ledger_hash
            in
            let next_ledger_hash =
              Option.value_map ledger_proof_opt
                ~f:(fun (proof, _) ->
                  Ledger_proof.statement proof |> Ledger_proof.statement_target
                  )
                ~default:previous_ledger_hash
            in
            let supply_increase =
              Option.value_map ledger_proof_opt
                ~f:(fun (proof, _) ->
                  (Ledger_proof.statement proof).supply_increase )
                ~default:Currency.Amount.zero
            in
            let blockchain_state =
              (* We use the time this proposal was supposed to happen at because
             if things are slower than expected, we may have entered the next
             slot and putting the **current** timestamp rather than the expected
             one will screw things up.

             [generate_transition] will log an error if the [current_time] has a
             different slot from the [scheduled_time]
          *)
              Blockchain_state.create_value ~timestamp:scheduled_time
                ~snarked_ledger_hash:next_ledger_hash
                ~staged_ledger_hash:next_staged_ledger_hash
            in
            let current_time =
              Time.now time_controller |> Time.to_span_since_epoch
              |> Time.Span.to_ms
            in
            measure "consensus generate_transition" (fun () ->
                Consensus_state_hooks.generate_transition
                  ~previous_protocol_state ~blockchain_state ~current_time
                  ~proposal_data
                  ~transactions:
                    ( Staged_ledger_diff.With_valid_signatures_and_proofs
                      .user_commands diff
                      :> User_command.t list )
                  ~snarked_ledger_hash:previous_ledger_hash ~supply_increase
                  ~logger ) )
      in
      lift_sync (fun () ->
          measure "making Snark and Internal transitions" (fun () ->
              let snark_transition =
                Snark_transition.create_value
                  ?sok_digest:
                    (Option.map ledger_proof_opt ~f:(fun (proof, _) ->
                         Ledger_proof.sok_digest proof ))
                  ?ledger_proof:
                    (Option.map ledger_proof_opt ~f:(fun (proof, _) ->
                         Ledger_proof.underlying_proof proof ))
                  ~supply_increase:
                    (Option.value_map ~default:Currency.Amount.zero
                       ~f:(fun (proof, _) ->
                         (Ledger_proof.statement proof).supply_increase )
                       ledger_proof_opt)
                  ~blockchain_state:
                    (Protocol_state.blockchain_state protocol_state)
                  ~consensus_transition:consensus_transition_data
                  ~proposer:self ~coinbase_amount
                  ~coinbase_state_body_hash:protocol_state_body_hash ()
              in
              let internal_transition =
                Internal_transition.create ~snark_transition
                  ~prover_state:
                    (Consensus.Data.Proposal_data.prover_state proposal_data)
                  ~staged_ledger_diff:(Staged_ledger_diff.forget diff)
              in
              let witness =
                { Pending_coinbase_witness.pending_coinbases=
                    Staged_ledger.pending_coinbase_collection staged_ledger
                ; is_new_stack }
              in
              Some (protocol_state, internal_transition, witness) ) )

let run ~logger ~prover ~verifier ~trust_system ~get_completed_work
    ~transaction_resource_pool ~time_controller ~keypairs
    ~consensus_local_state ~frontier_reader ~transition_writer
    ~set_next_proposal =
  trace_task "block_producer" (fun () ->
      let log_bootstrap_mode () =
        Logger.info logger ~module_:__MODULE__ ~location:__LOC__
          "Pausing block production while bootstrapping"
      in
      let module Breadcrumb = Transition_frontier.Breadcrumb in
      let propose ivar (keypair, scheduled_time, proposal_data) =
        let open Interruptible.Let_syntax in
        match Broadcast_pipe.Reader.peek frontier_reader with
        | None ->
            log_bootstrap_mode () ; Interruptible.return ()
        | Some frontier -> (
            let crumb = Transition_frontier.best_tip frontier in
            Logger.trace logger ~module_:__MODULE__ ~location:__LOC__
              ~metadata:[("breadcrumb", Breadcrumb.to_yojson crumb)]
              !"Producing new block with parent $breadcrumb%!" ;
            let previous_protocol_state, previous_protocol_state_proof =
              let transition : External_transition.Validated.t =
                Breadcrumb.validated_transition crumb
              in
              ( External_transition.Validated.protocol_state transition
              , External_transition.Validated.protocol_state_proof transition
              )
            in
            let transactions =
              Network_pool.Transaction_pool.Resource_pool.transactions
                transaction_resource_pool
            in
            trace_event "waiting for ivar..." ;
            let%bind () =
              Interruptible.lift (Deferred.return ()) (Ivar.read ivar)
            in
            let%bind next_state_opt =
              generate_next_state ~scheduled_time ~proposal_data
                ~previous_protocol_state ~time_controller
                ~staged_ledger:(Breadcrumb.staged_ledger crumb)
                ~transactions ~get_completed_work ~logger ~keypair
            in
            trace_event "next state generated" ;
            match next_state_opt with
            | None ->
                Interruptible.return ()
            | Some
                (protocol_state, internal_transition, pending_coinbase_witness)
              ->
                Debug_assert.debug_assert (fun () ->
                    [%test_result: [`Take | `Keep]]
                      (Consensus.Hooks.select
                         ~existing:
                           (Protocol_state.consensus_state
                              previous_protocol_state)
                         ~candidate:
                           (Protocol_state.consensus_state protocol_state)
                         ~logger)
                      ~expect:`Take
                      ~message:
                        "newly generated consensus states should be selected \
                         over their parent" ;
                    let root_consensus_state =
                      Transition_frontier.root frontier
                      |> Breadcrumb.consensus_state
                    in
                    [%test_result: [`Take | `Keep]]
                      (Consensus.Hooks.select ~existing:root_consensus_state
                         ~candidate:
                           (Protocol_state.consensus_state protocol_state)
                         ~logger)
                      ~expect:`Take
                      ~message:
                        "newly generated consensus states should be selected \
                         over the tf root" ) ;
                Interruptible.uninterruptible
                  (let open Deferred.Let_syntax in
                  let t0 = Time.now time_controller in
                  match%bind
                    measure "proving state transition valid" (fun () ->
                        Prover.prove prover ~prev_state:previous_protocol_state
                          ~prev_state_proof:previous_protocol_state_proof
                          ~next_state:protocol_state internal_transition
                          pending_coinbase_witness )
                  with
                  | Error err ->
                      Logger.error logger ~module_:__MODULE__ ~location:__LOC__
                        "Prover failed to prove freshly generated transition: \
                         $error"
                        ~metadata:
                          [ ("error", `String (Error.to_string_hum err))
                          ; ( "prev_state"
                            , Protocol_state.value_to_yojson
                                previous_protocol_state )
                          ; ( "prev_state_proof"
                            , Proof.to_yojson previous_protocol_state_proof )
                          ; ( "next_state"
                            , Protocol_state.value_to_yojson protocol_state )
                          ; ( "internal_transition"
                            , Internal_transition.to_yojson internal_transition
                            )
                          ; ( "pending_coinbase_witness"
                            , Pending_coinbase_witness.to_yojson
                                pending_coinbase_witness ) ] ;
                      return ()
                  | Ok protocol_state_proof -> (
                      let span = Time.diff (Time.now time_controller) t0 in
                      Logger.info logger ~module_:__MODULE__ ~location:__LOC__
                        ~metadata:
                          [ ( "proving_time"
                            , `Int (Time.Span.to_ms span |> Int64.to_int_exn)
                            ) ]
                        !"Protocol_state_proof proving time took: \
                          $proving_time%!" ;
                      let staged_ledger_diff =
                        Internal_transition.staged_ledger_diff
                          internal_transition
                      in
                      let transition_hash =
                        Protocol_state.hash protocol_state
                      in
                      let delta_transition_chain_proof =
                        Transition_chain_prover.prove
                          ~length:(Consensus.Constants.delta - 1)
                          ~frontier
                          (Protocol_state.hash previous_protocol_state)
                        |> Option.value_exn
                      in
                      let error_msg_prefix = "Validation failed: " in
                      let reason_for_failure =
                        " One possible reason could be a ledger-catchup is \
                         triggered before we produce a proof for the proposed \
                         transition."
                      in
                      match
                        External_transition.Validation.wrap
                          { With_hash.hash= transition_hash
                          ; data=
                              External_transition.create ~protocol_state
                                ~protocol_state_proof ~staged_ledger_diff
                                ~delta_transition_chain_proof }
                        |> External_transition.skip_time_received_validation
                             `This_transition_was_not_received_via_gossip
                        |> External_transition.skip_proof_validation
                             `This_transition_was_generated_internally
                        |> External_transition
                           .skip_delta_transition_chain_validation
                             `This_transition_was_not_received_via_gossip
                        |> Transition_frontier_validation
                           .validate_frontier_dependencies ~logger ~frontier
                      with
                      | Error `Already_in_frontier ->
                          Logger.error logger ~module_:__MODULE__
                            ~location:__LOC__
                            ~metadata:
                              [ ( "protocol_state"
                                , Protocol_state.value_to_yojson protocol_state
                                ) ]
                            "%sproposed transition is already in frontier"
                            error_msg_prefix ;
                          return ()
                      | Error `Not_selected_over_frontier_root ->
                          Logger.warn logger ~module_:__MODULE__
                            ~location:__LOC__
                            "%sproposed transition is not selected over the \
                             root of transition frontier.%s"
                            error_msg_prefix reason_for_failure ;
                          return ()
                      | Error `Parent_missing_from_frontier ->
                          Logger.warn logger ~module_:__MODULE__
                            ~location:__LOC__
                            "%sparent of proposed transition is missing from \
                             the frontier.%s"
                            error_msg_prefix reason_for_failure ;
                          return ()
                      | Ok transition -> (
                          let%bind breadcrumb_result =
                            Breadcrumb.build ~logger ~verifier ~trust_system
                              ~parent:crumb ~transition ~sender:None
                          in
                          let exn name =
                            raise
                              (Error.to_exn
                                 (Error.of_string
                                    (sprintf
                                       "Error building breadcrumb from \
                                        proposed transition: %s"
                                       name)))
                          in
                          match breadcrumb_result with
                          | Error (`Fatal_error e) ->
                              exn
                                (sprintf "fatal error -- %s" (Exn.to_string e))
                          | Error (`Invalid_staged_ledger_hash e) ->
                              exn
                                (sprintf "Invalid staged ledger hash -- %s"
                                   (Error.to_string_hum e))
                          | Error (`Invalid_staged_ledger_diff e) ->
                              (*Unexpected errors from staged_ledger are captured in `Fatal_error*)
                              Logger.error logger ~module_:__MODULE__
                                ~location:__LOC__
                                ~metadata:
                                  [ ( "diff"
                                    , Staged_ledger_diff.to_yojson
                                        staged_ledger_diff ) ]
                                !"Error building breadcrumb from proposed \
                                  transition. Invalid staged ledger diff -- %s"
                                (Error.to_string_hum e) ;
                              return ()
                          | Ok breadcrumb -> (
                              let metadata =
                                [ ( "state_hash"
                                  , State_hash.to_yojson transition_hash ) ]
                              in
                              Logger.info logger ~module_:__MODULE__
                                ~location:__LOC__
                                !"Submitting newly produced block $state_hash \
                                  to the transition frontier controller"
                                ~metadata ;
                              Coda_metrics.(
                                Counter.inc_one Proposer.blocks_proposed) ;
                              let%bind () =
                                Strict_pipe.Writer.write transition_writer
                                  breadcrumb
                              in
                              Logger.debug logger ~module_:__MODULE__
                                ~location:__LOC__ ~metadata
                                "Waiting for transition $state_hash to be \
                                 inserted into frontier" ;
                              Deferred.choose
                                [ Deferred.choice
                                    (Transition_frontier.wait_for_transition
                                       frontier transition_hash)
                                    (Fn.const `Transition_accepted)
                                ; Deferred.choice
                                    ( Time.Timeout.create time_controller
                                        (* We allow up to 15 seconds for the transition to make its way from the transition_writer to the frontier.
                                  This value is chosen to be reasonably generous. In theory, this should not take terribly long. But long
                                  cycles do happen in our system, and with medium curves those long cycles can be substantial. *)
                                        (Time.Span.of_ms 20000L)
                                        ~f:(Fn.const ())
                                    |> Time.Timeout.to_deferred )
                                    (Fn.const `Timed_out) ]
                              >>| function
                              | `Transition_accepted ->
                                  Logger.info logger ~module_:__MODULE__
                                    ~location:__LOC__ ~metadata
                                    "Generated transition $state_hash was \
                                     accepted into transition frontier"
                              | `Timed_out ->
                                  let str =
                                    "Timed out waiting for generated \
                                     transition $state_hash to enter \
                                     transition frontier. Continuing to \
                                     produce new blocks anyway. This may mean \
                                     your CPU is overloaded. Consider \
                                     disabling `-run-snark-worker` if it's \
                                     configured."
                                  in
                                  (* FIXME #3167: this should be fatal, and more importantly, shouldn't happen. *)
                                  Logger.error logger ~module_:__MODULE__
                                    ~location:__LOC__ ~metadata "%s" str ) ) ))
            )
      in
      let proposal_supervisor = Singleton_supervisor.create ~task:propose in
      let scheduler = Singleton_scheduler.create time_controller in
      let rec check_for_proposal () =
        trace_recurring_task "check for proposal" (fun () ->
            (* See if we want to change keypairs *)
            let keypairs =
              match Agent.get keypairs with
              | keypairs, `Different ->
                  (* Perform proposer swap since we have new keypairs *)
                  Consensus.Data.Local_state.proposer_swap
                    consensus_local_state
                    ( Keypair.And_compressed_pk.Set.to_list keypairs
                    |> List.map ~f:snd |> Public_key.Compressed.Set.of_list )
                    (Time.now time_controller) ;
                  keypairs
              | keypairs, `Same ->
                  keypairs
            in
            (* Begin proposal checking *)
            match Broadcast_pipe.Reader.peek frontier_reader with
            | None ->
                log_bootstrap_mode () ;
                don't_wait_for
                  (let%map () =
                     Broadcast_pipe.Reader.iter_until frontier_reader
                       ~f:(Fn.compose Deferred.return Option.is_some)
                   in
                   check_for_proposal ())
            | Some transition_frontier -> (
                let consensus_state =
                  Transition_frontier.best_tip transition_frontier
                  |> Breadcrumb.consensus_state
                in
                assert (
                  Consensus.Hooks.required_local_state_sync ~consensus_state
                    ~local_state:consensus_local_state
                  = None ) ;
                let now = Time.now time_controller in
                let next_proposal =
                  measure "asking conensus what to do" (fun () ->
                      Consensus.Hooks.next_proposal (time_to_ms now)
                        consensus_state ~local_state:consensus_local_state
                        ~keypairs ~logger )
                in
                set_next_proposal next_proposal ;
                match next_proposal with
                | `Check_again time ->
                    Singleton_scheduler.schedule scheduler (time_of_ms time)
                      ~f:check_for_proposal
                | `Propose_now (keypair, data) ->
                    Coda_metrics.(Counter.inc_one Proposer.slots_won) ;
                    Interruptible.finally
                      (Singleton_supervisor.dispatch proposal_supervisor
                         (keypair, now, data))
                      ~f:check_for_proposal
                    |> ignore
                | `Propose (time, keypair, data) ->
                    Coda_metrics.(Counter.inc_one Proposer.slots_won) ;
                    let scheduled_time = time_of_ms time in
                    Singleton_scheduler.schedule scheduler scheduled_time
                      ~f:(fun () ->
                        ignore
                          (Interruptible.finally
                             (Singleton_supervisor.dispatch proposal_supervisor
                                (keypair, scheduled_time, data))
                             ~f:check_for_proposal) ) ) )
      in
      let start () =
        (* Schedule to wake up immediately on the next tick of the proposer
         * instead of immediately mutating local_state here as there could be a
         * race.
         *
         * Given that rescheduling takes the min of the two timeouts, we won't
         * erase this timeout even if the last run of the proposer wants to wait
         * for a long while.
         * *)
        Agent.on_update keypairs ~f:(fun _new_keypairs ->
            Singleton_scheduler.schedule scheduler (Time.now time_controller)
              ~f:check_for_proposal ) ;
        check_for_proposal ()
      in
      (* if the proposer starts before genesis, sleep until genesis *)
      let now = Time.now time_controller in
      if Time.( >= ) now Consensus.Constants.genesis_state_timestamp then
        start ()
      else
        let time_till_genesis =
          Time.diff Consensus.Constants.genesis_state_timestamp now
        in
        Logger.warn logger ~module_:__MODULE__ ~location:__LOC__
          ~metadata:
            [ ( "time_till_genesis"
              , `Int (Int64.to_int_exn (Time.Span.to_ms time_till_genesis)) )
            ]
          "Node started before genesis: waiting $time_till_genesis \
           milliseconds before starting block producer" ;
        ignore
          (Time.Timeout.create time_controller time_till_genesis ~f:(fun _ ->
               start () )) )
