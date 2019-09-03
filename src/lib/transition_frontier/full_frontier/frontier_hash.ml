open Core_kernel
open Coda_base
open Signature_lib

module Make (Inputs : Inputs.With_diff_intf) : Coda_intf.Transition_frontier_incremental_hash_intf with type 'mutant lite_diff := 'mutant Inputs.Diff.Lite.t = struct
  open Inputs

  open Digestif.SHA256

  type nonrec t = t

  let to_yojson hash = [%derive.to_yojson: string] (to_raw_string hash)
  let of_yojson json =
    let open Result.Let_syntax in
    let%bind str = [%derive.of_yojson: string] json in
    match of_raw_string_opt str with
    | Some hash -> Ok hash
    | None -> Error "invalid raw hash"

  type transition = { source: t; target: t }

  include Binable.Of_stringable (struct	
   type nonrec t = t	

    let of_string = of_hex	

    let to_string = to_hex	
  end)	

  let equal t1 t2 = equal t1 t2	

  let empty = digest_string ""	

  let merge_string t1 string = digestv_string [to_hex t1; string]	

  let to_string = to_raw_string	

  let merge_state_hash acc state_hash =
    merge_string acc (State_hash.to_bytes state_hash)

  (* This currently only hashes the creator of the staged ledger
   * diff. The previous hash is already encapsulated in the
   * transition frontier incremental diff hash via the state
   * hash since the Blockchain_state contains the previous
   * staged ledger hash already. The only information missing
   * from this is the actual contents of the diff itself
   * (the transactions). This can't be included in O(1) as is
   * since it is not precomputed, so it is left out here for now. *)
  let merge_staged_ledger_diff acc diff =
    (* TODO: hash target ledger hash? (does this need to be computed?) *)
    merge_string
      acc
      (Public_key.Compressed.to_string (Staged_ledger_diff.creator diff))

  let merge_transition acc transition =
    merge_staged_ledger_diff acc
      (External_transition.Validated.staged_ledger_diff transition)

  let merge_with_hash acc with_hash ~merge_data =
    merge_data
      (merge_state_hash acc (With_hash.hash with_hash))
      (With_hash.data with_hash)

  (*
  let merge_breadcrumb acc breadcrumb =
    merge_string
      (merge_string
        (merge_with_hash ~merge_data:merge_transition acc (Breadcrumb.transition_with_hash breadcrumb))
        (Ledger_hash.to_bytes (Ledger.merkle_root (Staged_ledger.ledger (Breadcrumb.staged_ledger breadcrumb)))))
      (Int.to_string @@ Bool.to_int (Breadcrumb.just_emitted_a_proof breadcrumb))
  *)

  let merge_pending_coinbase _ _ = failwith "TODO"

  let merge_scan_state _ _ = failwith "TODO"

  let merge_root_data acc {Diff.hash; scan_state; pending_coinbase} =
    merge_pending_coinbase
      (merge_scan_state
        (merge_state_hash acc hash)
        scan_state)
      pending_coinbase


  let merge_diff : type mutant. t -> (Diff.lite, mutant) Diff.t -> t =
    fun acc diff ->
      match diff with
      | New_node (Lite node) -> merge_with_hash ~merge_data:merge_transition acc node
      | Root_transitioned {new_root; garbage} ->
          List.fold_left garbage ~init:(merge_root_data acc new_root) ~f:merge_state_hash
      | Best_tip_changed best_tip -> merge_state_hash acc best_tip
      (* Despite the fact that OCaml won't allow you to pass in a (full, mutant) Diff.t to this function,
       * the exhaustiveness checker is not convinced. This case cannot be reached. *)
      | _ -> failwith "impossible"

  let merge_mutant : type mutant. t -> mutant Diff.Lite.t -> mutant -> t =
    fun acc diff mutant ->
      match diff with
      | New_node _ -> acc
      | Root_transitioned _ -> merge_state_hash acc mutant
      | Best_tip_changed _ -> merge_state_hash acc mutant

  let merge_diff : type mutant. t -> mutant Diff.Lite.t -> mutant -> t =
    fun acc diff mutant ->
      merge_mutant
        (merge_diff acc diff)
        diff
        mutant
end