open Core_kernel
open Async
open Coda_base
open Coda_transition

module type Inputs_intf = sig
  module Transition_frontier : module type of Transition_frontier

  module Best_tip_prover :
    Coda_intf.Best_tip_prover_intf
    with type transition_frontier := Transition_frontier.t
end

module Make (Inputs : Inputs_intf) :
  Coda_intf.Sync_handler_intf
  with type transition_frontier := Inputs.Transition_frontier.t = struct
  open Inputs

  let find_in_root_history frontier state_hash =
    let open Transition_frontier.Extensions in
    let root_history =
      get_extension (Transition_frontier.extensions frontier) Root_history
    in
    Root_history.lookup root_history state_hash

  let get_breadcrumb_ledgers frontier =
    List.map
      (Transition_frontier.all_breadcrumbs frontier)
      ~f:
        (Fn.compose Staged_ledger.ledger
           Transition_frontier.Breadcrumb.staged_ledger)

  let get_ledger_by_hash ~frontier ledger_hash =
    let ledger_breadcrumbs =
      Sequence.of_lazy
        (lazy (Sequence.of_list @@ get_breadcrumb_ledgers frontier))
    in
    let root_ledger =
      Ledger.Any_ledger.cast
        (module Ledger.Db)
        (Transition_frontier.root_snarked_ledger frontier)
    in
    let mask =
      Ledger.Maskable.register_mask root_ledger (Ledger.Mask.create ())
    in
    Sequence.append (Sequence.singleton mask) ledger_breadcrumbs
    |> Sequence.find ~f:(fun ledger ->
           Ledger_hash.equal (Ledger.merkle_root ledger) ledger_hash )

  let answer_query :
         frontier:Inputs.Transition_frontier.t
      -> Ledger_hash.t
      -> Sync_ledger.Query.t Envelope.Incoming.t
      -> logger:Logger.t
      -> trust_system:Trust_system.t
      -> Sync_ledger.Answer.t Option.t Deferred.t =
   fun ~frontier hash query ~logger ~trust_system ->
    match get_ledger_by_hash ~frontier hash with
    | None ->
        return None
    | Some ledger ->
        let responder =
          Sync_ledger.Mask.Responder.create ledger ignore ~logger ~trust_system
        in
        Sync_ledger.Mask.Responder.answer_query responder query

  let get_staged_ledger_aux_and_pending_coinbases_at_hash ~frontier state_hash
      =
    let open Option.Let_syntax in
    let%map scan_state, pending_coinbases =
      Option.merge
        (let%map breadcrumb = Transition_frontier.find frontier state_hash in
         let staged_ledger =
           Transition_frontier.Breadcrumb.staged_ledger breadcrumb
         in
         let scan_state = Staged_ledger.scan_state staged_ledger in
         let pending_coinbase =
           Staged_ledger.pending_coinbase_collection staged_ledger
         in
         (scan_state, pending_coinbase))
        (let%map {scan_state; pending_coinbase; _} =
           find_in_root_history frontier state_hash
         in
         (scan_state, pending_coinbase))
        ~f:Fn.const
    in
    (scan_state, pending_coinbases)

  let get_transition_chain ~frontier hashes =
    let open Option.Let_syntax in
    Option.all
    @@ List.map hashes ~f:(fun hash ->
           let%map validated_transition =
             Option.merge
               Transition_frontier.(
                 find frontier hash >>| Breadcrumb.validated_transition)
               (find_in_root_history frontier hash >>| fun x -> x.transition)
               ~f:Fn.const
           in
           External_transition.Validation.forget_validation
             validated_transition )

  module Root = struct
    let prove ~logger ~frontier seen_consensus_state =
      let open Option.Let_syntax in
      let%bind best_tip_with_witness =
        Best_tip_prover.prove ~logger frontier
      in
      let is_tip_better =
        Consensus.Hooks.select
          ~logger:
            (Logger.extend logger [("selection_context", `String "Root.prove")])
          ~existing:
            (External_transition.consensus_state best_tip_with_witness.data)
          ~candidate:seen_consensus_state
        = `Keep
      in
      let%map () = Option.some_if is_tip_better () in
      best_tip_with_witness

    let verify ~logger ~verifier observed_state peer_root =
      let open Deferred.Result.Let_syntax in
      let%bind ( (`Root _, `Best_tip (best_tip_transition, _)) as
               verified_witness ) =
        Best_tip_prover.verify ~verifier peer_root
      in
      let is_before_best_tip candidate =
        Consensus.Hooks.select
          ~logger:
            (Logger.extend logger [("selection_context", `String "Root.verify")])
          ~existing:
            (External_transition.consensus_state best_tip_transition.data)
          ~candidate
        = `Keep
      in
      let%map () =
        Deferred.return
          (Result.ok_if_true
             (is_before_best_tip observed_state)
             ~error:
               (Error.createf
                  !"Peer lied about it's best tip %{sexp:State_hash.t}"
                  best_tip_transition.hash))
      in
      verified_witness
  end

  module Bootstrappable_best_tip = struct
    let prove ~logger ~should_select_tip ~frontier clients_consensus_state =
      let open Option.Let_syntax in
      let%bind best_tip_with_witness =
        Best_tip_prover.prove ~logger frontier
      in
      let%map () =
        Option.some_if
          (should_select_tip ~existing:clients_consensus_state
             ~candidate:
               (External_transition.consensus_state best_tip_with_witness.data)
             ~logger:
               (Logger.extend logger
                  [ ( "selection_context"
                    , `String "Bootstrappable_best_tip.prove" ) ]))
          ()
      in
      best_tip_with_witness

    let verify ~logger ~should_select_tip ~verifier existing_state
        ( {Proof_carrying_data.data= best_tip; proof= _merkle_list, _root} as
        peer_best_tip ) =
      let open Deferred.Or_error.Let_syntax in
      let%bind () =
        Deferred.return
          (Result.ok_if_true
             ~error:
               (Error.of_string
                  "Peer's best tip did not cause you to bootstrap")
             (should_select_tip ~existing:existing_state
                ~candidate:(External_transition.consensus_state best_tip)
                ~logger:
                  (Logger.extend logger
                     [ ( "selection_context"
                       , `String "Bootstrappable_best_tip.verify" ) ])))
      in
      Best_tip_prover.verify ~verifier peer_best_tip

    module For_tests = struct
      let prove = prove

      let verify = verify
    end

    let prove = prove ~should_select_tip:Consensus.Hooks.should_bootstrap

    let verify = verify ~should_select_tip:Consensus.Hooks.should_bootstrap
  end
end

include Make (struct
  module Transition_frontier = Transition_frontier
  module Best_tip_prover = Best_tip_prover
end)
