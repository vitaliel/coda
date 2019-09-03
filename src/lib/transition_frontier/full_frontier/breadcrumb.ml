open Async_kernel
open Core_kernel
open Coda_base
open Coda_state

module Make
  (Inputs : Coda_intf.Inputs_intf)
  : Coda_intf.Transition_frontier_breadcrumb_intf
    with type mostly_validated_external_transition :=
                ( [`Time_received] * Truth.true_t
                , [`Proof] * Truth.true_t
                , [`Frontier_dependencies] * Truth.true_t
                , [`Staged_ledger_diff] * Truth.false_t )
                Inputs.External_transition.Validation.with_transition
     and type external_transition_validated := Inputs.External_transition.Validated.t
     and type staged_ledger := Inputs.Staged_ledger.t
     and type verifier := Inputs.Verifier.t = struct
  open Inputs

  type t =
    { transition_with_hash:
        (External_transition.Validated.t, State_hash.t) With_hash.t
    ; mutable staged_ledger: Staged_ledger.t sexp_opaque
    ; just_emitted_a_proof: bool }
  [@@deriving sexp, fields]

  let to_yojson {transition_with_hash; staged_ledger= _; just_emitted_a_proof}
      =
    `Assoc
      [ ( "transition_with_hash"
        , With_hash.to_yojson External_transition.Validated.to_yojson
            State_hash.to_yojson transition_with_hash )
      ; ("staged_ledger", `String "<opaque>")
      ; ("just_emitted_a_proof", `Bool just_emitted_a_proof) ]

  let create transition_with_hash staged_ledger =
    {transition_with_hash; staged_ledger; just_emitted_a_proof= false}

  let copy t = {t with staged_ledger= Staged_ledger.copy t.staged_ledger}

  module Staged_ledger_validation =
    External_transition.Staged_ledger_validation (Staged_ledger)

  let build ~logger ~verifier ~trust_system ~parent
      ~transition:transition_with_validation ~sender =
    O1trace.measure "Breadcrumb.build" (fun () ->
        let open Deferred.Let_syntax in
        match%bind
          Staged_ledger_validation.validate_staged_ledger_diff ~logger
            ~verifier ~parent_staged_ledger:parent.staged_ledger
            transition_with_validation
        with
        | Ok
            ( `Just_emitted_a_proof just_emitted_a_proof
            , `External_transition_with_validation
                fully_valid_external_transition
            , `Staged_ledger transitioned_staged_ledger ) ->
            return
              (Ok
                 { transition_with_hash=
                     External_transition.Validation.lift
                       fully_valid_external_transition
                 ; staged_ledger= transitioned_staged_ledger
                 ; just_emitted_a_proof })
        | Error (`Invalid_staged_ledger_diff errors) ->
            let reasons =
              String.concat ~sep:" && "
                (List.map errors ~f:(function
                  | `Incorrect_target_staged_ledger_hash ->
                      "staged ledger hash"
                  | `Incorrect_target_snarked_ledger_hash ->
                      "snarked ledger hash" ))
            in
            let message =
              "invalid staged ledger diff: incorrect " ^ reasons
            in
            let%map () =
              match sender with
              | None | Some Envelope.Sender.Local ->
                  return ()
              | Some (Envelope.Sender.Remote inet_addr) ->
                  Trust_system.(
                    record trust_system logger inet_addr
                      Actions.
                        (Gossiped_invalid_transition, Some (message, [])))
            in
            Error (`Invalid_staged_ledger_hash (Error.of_string message))
        | Error
            (`Staged_ledger_application_failed
              (Staged_ledger.Staged_ledger_error.Unexpected e)) ->
            return (Error (`Fatal_error (Error.to_exn e)))
        | Error (`Staged_ledger_application_failed staged_ledger_error) ->
            let%map () =
              match sender with
              | None | Some Envelope.Sender.Local ->
                  return ()
              | Some (Envelope.Sender.Remote inet_addr) ->
                  let error_string =
                    Staged_ledger.Staged_ledger_error.to_string
                      staged_ledger_error
                  in
                  let make_actions action =
                    ( action
                    , Some
                        ( "Staged_ledger error: $error"
                        , [("error", `String error_string)] ) )
                  in
                  let open Trust_system.Actions in
                  (* TODO : refine these actions, issue 2375 *)
                  let open Staged_ledger.Pre_diff_info.Error in
                  let action =
                    match staged_ledger_error with
                    | Invalid_proof _ ->
                        make_actions Sent_invalid_proof
                    | Pre_diff (Bad_signature _) ->
                        make_actions Sent_invalid_signature
                    | Pre_diff _ | Bad_prev_hash _ | Non_zero_fee_excess _ ->
                        make_actions Gossiped_invalid_transition
                    | Unexpected _ ->
                        failwith
                          "build: Unexpected staged ledger error should \
                           have been caught in another pattern"
                  in
                  Trust_system.record trust_system logger inet_addr action
            in
            Error
              (`Invalid_staged_ledger_diff
                (Staged_ledger.Staged_ledger_error.to_error
                   staged_ledger_error)) )

  let external_transition {transition_with_hash; _} =
    With_hash.data transition_with_hash

  let state_hash {transition_with_hash; _} =
    With_hash.hash transition_with_hash

  let parent_hash {transition_with_hash; _} =
    With_hash.data transition_with_hash
    |> External_transition.Validated.protocol_state
    |> Protocol_state.previous_state_hash

  let equal breadcrumb1 breadcrumb2 =
    State_hash.equal (state_hash breadcrumb1) (state_hash breadcrumb2)

  let compare breadcrumb1 breadcrumb2 =
    State_hash.compare (state_hash breadcrumb1) (state_hash breadcrumb2)

  let hash = Fn.compose State_hash.hash state_hash

  let consensus_state {transition_with_hash; _} =
    With_hash.data transition_with_hash
    |> External_transition.Validated.protocol_state
    |> Protocol_state.consensus_state

  let blockchain_state {transition_with_hash; _} =
    With_hash.data transition_with_hash
    |> External_transition.Validated.protocol_state
    |> Protocol_state.blockchain_state

  let name t =
    Visualization.display_short_sexp (module State_hash) @@ state_hash t

  type display =
    { state_hash: string
    ; blockchain_state: Blockchain_state.display
    ; consensus_state: Consensus.Data.Consensus_state.display
    ; parent: string }
  [@@deriving yojson]

  let display t =
    let blockchain_state = Blockchain_state.display (blockchain_state t) in
    let consensus_state = consensus_state t in
    let parent =
      Visualization.display_short_sexp (module State_hash) @@ parent_hash t
    in
    { state_hash= name t
    ; blockchain_state
    ; consensus_state= Consensus.Data.Consensus_state.display consensus_state
    ; parent }

  let to_user_commands
      {transition_with_hash= {data= external_transition; _}; _} =
    let open External_transition.Validated in
    let open Staged_ledger_diff in
    user_commands @@ staged_ledger_diff external_transition
end