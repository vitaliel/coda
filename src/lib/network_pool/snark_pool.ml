open Core_kernel
open Async
open Pipe_lib

module type S = sig
  type ledger_proof

  type transaction_snark_statement

  type transaction_snark_work_statement

  type transaction_snark_work_checked

  type transition_frontier

  type transaction_snark_work_info

  module Resource_pool : sig
    include
      Intf.Snark_resource_pool_intf
      with type ledger_proof := ledger_proof
       and type work := transaction_snark_work_statement
       and type transition_frontier := transition_frontier
       and type work_info := transaction_snark_work_info

    val remove_solved_work : t -> transaction_snark_work_statement -> unit

    module Diff :
      Intf.Snark_pool_diff_intf
      with type ledger_proof := ledger_proof
       and type work := transaction_snark_work_statement
       and type resource_pool := t
  end

  module For_tests : sig
    val get_rebroadcastable :
         Resource_pool.t
      -> is_expired:(Time.t -> [`Expired | `Ok])
      -> Resource_pool.Diff.t list
  end

  include
    Intf.Network_pool_base_intf
    with type resource_pool := Resource_pool.t
     and type resource_pool_diff := Resource_pool.Diff.t
     and type transition_frontier := transition_frontier
     and type config := Resource_pool.Config.t

  val get_completed_work :
       t
    -> transaction_snark_work_statement
    -> transaction_snark_work_checked option

  val load :
       config:Resource_pool.Config.t
    -> logger:Logger.t
    -> disk_location:string
    -> incoming_diffs:Resource_pool.Diff.t Envelope.Incoming.t
                      Linear_pipe.Reader.t
    -> frontier_broadcast_pipe:transition_frontier option
                               Broadcast_pipe.Reader.t
    -> t Deferred.t

  val add_completed_work :
       t
    -> ( ('a, 'b, 'c) Snark_work_lib.Work.Single.Spec.t
         Snark_work_lib.Work.Spec.t
       , ledger_proof )
       Snark_work_lib.Work.Result.t
    -> unit Deferred.t
end

module type Transition_frontier_intf = sig
  type work

  type t

  module Extensions : sig
    module Work : sig
      type t = work [@@deriving sexp]

      module Stable : sig
        module V1 : sig
          type nonrec t = t [@@deriving sexp, bin_io]

          include Hashable.S_binable with type t := t
        end
      end

      include Hashable.S with type t := t
    end
  end

  val snark_pool_refcount_pipe :
    t -> (int * int Extensions.Work.Table.t) Pipe_lib.Broadcast_pipe.Reader.t
end

module Make
    (Transition_frontier : Transition_frontier_intf
                           with type work := Transaction_snark_work.Statement.t) :
  S
  with type transaction_snark_statement := Transaction_snark.Statement.t
   and type transaction_snark_work_statement :=
              Transaction_snark_work.Statement.t
   and type transaction_snark_work_checked := Transaction_snark_work.Checked.t
   and type transition_frontier := Transition_frontier.t
   and type ledger_proof := Ledger_proof.t
   and type transaction_snark_work_info := Transaction_snark_work.Info.t =
struct
  module Statement_table = Transaction_snark_work.Statement.Stable.V1.Table

  module Resource_pool = struct
    module T = struct
      (* TODO : Version this type *)
      type serializable =
        { all:
            Ledger_proof.Stable.V1.t One_or_two.Stable.V1.t
            Priced_proof.Stable.V1.t
            Statement_table.t
              (** Every SNARK in the pool *)
        ; rebroadcastable:
            ( Ledger_proof.Stable.V1.t One_or_two.Stable.V1.t
              Priced_proof.Stable.V1.t
            * Time.Stable.With_utc_sexp.V2.t )
            Statement_table.t
              (** Rebroadcastable SNARKs generated on this machine, along with
                  when they were first added. *)
        }
      [@@deriving sexp, bin_io]

      module Config = struct
        type t =
          { trust_system: Trust_system.t sexp_opaque
          ; verifier: Verifier.t sexp_opaque }
        [@@deriving sexp, make]
      end

      type t =
        { snark_tables: serializable
        ; mutable ref_table: int Statement_table.t option
        ; config: Config.t
        ; logger: Logger.t sexp_opaque }
      [@@deriving sexp]

      let make_config = Config.make

      let of_serializable tables ~config ~logger : t =
        {snark_tables= tables; ref_table= None; config; logger}

      let removed_breadcrumb_wait = 10

      let snark_pool_json t : Yojson.Safe.json =
        `List
          (Statement_table.fold ~init:[] t.snark_tables.all
             ~f:(fun ~key ~data:{proof= _; fee= {fee; prover}} acc ->
               let work_ids =
                 Transaction_snark_work.Statement.compact_json key
               in
               `Assoc
                 [ ("work_ids", work_ids)
                 ; ("fee", Currency.Fee.Stable.V1.to_yojson fee)
                 ; ( "prover"
                   , Signature_lib.Public_key.Compressed.Stable.V1.to_yojson
                       prover ) ]
               :: acc ))

      let all_completed_work (t : t) : Transaction_snark_work.Info.t list =
        Statement_table.fold ~init:[] t.snark_tables.all
          ~f:(fun ~key ~data:{proof= _; fee= {fee; prover}} acc ->
            let work_ids = Transaction_snark_work.Statement.work_ids key in
            {Transaction_snark_work.Info.statements= key; work_ids; fee; prover}
            :: acc )

      (** True when there is no active transition_frontier or
          when the refcount for the given work is 0 *)
      let work_is_referenced t work =
        match t.ref_table with
        | None ->
            true
        | Some ref_table -> (
          match Statement_table.find ref_table work with
          | None ->
              false
          | Some _ ->
              true )

      let listen_to_frontier_broadcast_pipe frontier_broadcast_pipe (t : t) =
        (* start with empty ref table *)
        t.ref_table <- None ;
        let tf_deferred =
          Broadcast_pipe.Reader.iter frontier_broadcast_pipe ~f:(function
            | Some tf ->
                (* Start the count at the max so we flush after reconstructing
                   the transition_frontier *)
                let removedCounter = ref removed_breadcrumb_wait in
                let pipe = Transition_frontier.snark_pool_refcount_pipe tf in
                let deferred =
                  Broadcast_pipe.Reader.iter pipe
                    ~f:(fun (removed, refcount_table) ->
                      t.ref_table <- Some refcount_table ;
                      removedCounter := !removedCounter + removed ;
                      if !removedCounter < removed_breadcrumb_wait then
                        return ()
                      else (
                        removedCounter := 0 ;
                        Statement_table.filter_keys_inplace
                          t.snark_tables.rebroadcastable ~f:(fun work ->
                            (* Rebroadcastable should always be a subset of all. *)
                            assert (Hashtbl.mem t.snark_tables.all work) ;
                            work_is_referenced t work ) ;
                        Statement_table.filter_keys_inplace t.snark_tables.all
                          ~f:(work_is_referenced t) ;
                        return
                          (*when snark works removed from the pool*)
                          Coda_metrics.(
                            Gauge.set Snark_work.snark_pool_size
                              ( Float.of_int
                              @@ Hashtbl.length t.snark_tables.all )) ) )
                in
                deferred
            | None ->
                t.ref_table <- None ;
                return () )
        in
        Deferred.don't_wait_for tf_deferred

      let create ~frontier_broadcast_pipe ~config ~logger =
        let t =
          { snark_tables=
              { all= Statement_table.create ()
              ; rebroadcastable= Statement_table.create () }
          ; logger
          ; config
          ; ref_table= None }
        in
        listen_to_frontier_broadcast_pipe frontier_broadcast_pipe t ;
        t

      let get_logger t = t.logger

      let request_proof t = Statement_table.find t.snark_tables.all

      let add_snark ?(is_local = false) t ~work
          ~(proof : Ledger_proof.t One_or_two.t) ~fee =
        if work_is_referenced t work then (
          (*Note: fee against existing proofs and the new proofs are checked in
          Diff.apply which calls this function*)
          Hashtbl.set t.snark_tables.all ~key:work ~data:{proof; fee} ;
          if is_local then
            Hashtbl.set t.snark_tables.rebroadcastable ~key:work
              ~data:({proof; fee}, Time.now ())
          else
            (* Stop rebroadcasting locally generated snarks if they are
               overwritten. No-op if there is no rebroadcastable SNARK with that
               statement. *)
            Hashtbl.remove t.snark_tables.rebroadcastable work ;
          (*when snark work is added to the pool*)
          Coda_metrics.(
            Gauge.set Snark_work.snark_pool_size
              (Float.of_int @@ Hashtbl.length t.snark_tables.all)) ;
          `Added )
        else (
          if is_local then
            Logger.warn t.logger ~module_:__MODULE__ ~location:__LOC__
              "Rejecting locally generated snark work $stmt, statement not \
               referenced"
              ~metadata:
                [ ( "stmt"
                  , One_or_two.to_yojson Transaction_snark.Statement.to_yojson
                      work ) ] ;
          `Statement_not_referenced )

      let verify_and_act t ~work ~sender =
        let statements, priced_proof = work in
        let open Deferred.Or_error.Let_syntax in
        let {Priced_proof.proof= proofs; fee= {prover; fee}} = priced_proof in
        let trust_record =
          Trust_system.record_envelope_sender t.config.trust_system t.logger
            sender
        in
        let log_and_punish ?(punish = true) statement e =
          let metadata =
            [ ("work_id", `Int (Transaction_snark.Statement.hash statement))
            ; ("prover", Signature_lib.Public_key.Compressed.to_yojson prover)
            ; ("fee", Currency.Fee.to_yojson fee)
            ; ("error", `String (Error.to_string_hum e)) ]
          in
          Logger.error t.logger ~module_:__MODULE__ ~location:__LOC__ ~metadata
            "Error verifying transaction snark: $error" ;
          if punish then
            trust_record
              ( Trust_system.Actions.Sent_invalid_proof
              , Some ("Error verifying transaction snark: $error", metadata) )
          else Deferred.return ()
        in
        let message = Coda_base.Sok_message.create ~fee ~prover in
        let verify ~proof ~statement =
          let open Deferred.Let_syntax in
          let statement_eq a b =
            Int.(Transaction_snark.Statement.compare a b = 0)
          in
          if not (statement_eq (Ledger_proof.statement proof) statement) then
            let e = Error.of_string "Statement and proof do not match" in
            let%map () = log_and_punish statement e in
            Error e
          else
            match%bind
              Verifier.verify_transaction_snark t.config.verifier proof
                ~message
            with
            | Ok true ->
                Deferred.Or_error.return ()
            | Ok false ->
                (*Invalid proof*)
                let e = Error.of_string "Invalid proof" in
                let%map () = log_and_punish statement e in
                Error e
            | Error e ->
                (* Verifier crashed or other errors at our end. Don't punish the peer*)
                let%map () = log_and_punish ~punish:false statement e in
                Error e
        in
        let%bind pairs = One_or_two.zip statements proofs |> Deferred.return in
        One_or_two.Deferred_result.fold ~init:() pairs
          ~f:(fun _ (statement, proof) ->
            let start = Time.now () in
            let res = verify ~proof ~statement in
            let time_ms =
              Time.abs_diff (Time.now ()) start |> Time.Span.to_ms
            in
            Logger.trace t.logger ~module_:__MODULE__ ~location:__LOC__
              ~metadata:
                [ ("work_id", `Int (Transaction_snark.Statement.hash statement))
                ; ("time", `Float time_ms) ]
              "Verification of work $work_id took $time ms" ;
            res )
    end

    include T
    module Diff =
      Snark_pool_diff.Make
        (Ledger_proof.Stable.V1)
        (Transaction_snark_work.Statement)
        (Transaction_snark_work.Info)
        (Transition_frontier)
        (T)

    let get_rebroadcastable t ~is_expired =
      Hashtbl.filteri_inplace t.snark_tables.rebroadcastable
        ~f:(fun ~key:stmt ~data:(_proof, time) ->
          match is_expired time with
          | `Expired ->
              Logger.debug t.logger ~module_:__MODULE__ ~location:__LOC__
                "No longer rebroadcasting SNARK with statement $stmt, it was \
                 added at $time its rebroadcast period is now expired"
                ~metadata:
                  [ ( "stmt"
                    , One_or_two.to_yojson
                        Transaction_snark.Statement.to_yojson stmt )
                  ; ( "time"
                    , `String (Time.to_string_abs ~zone:Time.Zone.utc time) )
                  ] ;
              false
          | `Ok ->
              true ) ;
      Hashtbl.to_alist t.snark_tables.rebroadcastable
      |> List.map ~f:(fun (stmt, (snark, _time)) ->
             Diff.Stable.Latest.Add_solved_work (stmt, snark) )

    let remove_solved_work t work =
      Statement_table.remove t.snark_tables.all work ;
      Statement_table.remove t.snark_tables.rebroadcastable work
  end

  include Network_pool_base.Make (Transition_frontier) (Resource_pool)

  module For_tests = struct
    let get_rebroadcastable = Resource_pool.get_rebroadcastable
  end

  let get_completed_work t statement =
    Option.map
      (Resource_pool.request_proof (resource_pool t) statement)
      ~f:(fun Priced_proof.{proof; fee= {fee; prover}} ->
        Transaction_snark_work.Checked.create_unsafe
          {Transaction_snark_work.fee; proofs= proof; prover} )

  let load ~config ~logger ~disk_location ~incoming_diffs
      ~frontier_broadcast_pipe =
    match%map
      Async.Reader.load_bin_prot disk_location
        Resource_pool.bin_reader_serializable
    with
    | Ok snark_table ->
        let pool = Resource_pool.of_serializable snark_table ~config ~logger in
        let network_pool =
          of_resource_pool_and_diffs pool ~logger ~incoming_diffs
        in
        Resource_pool.listen_to_frontier_broadcast_pipe frontier_broadcast_pipe
          pool ;
        network_pool
    | Error _e ->
        create ~config ~logger ~incoming_diffs ~frontier_broadcast_pipe

  open Snark_work_lib.Work

  let add_completed_work t
      (res : (('a, 'b, 'c) Single.Spec.t Spec.t, Ledger_proof.t) Result.t) =
    apply_and_broadcast t
      (Envelope.Incoming.wrap
         ~data:
           (Resource_pool.Diff.Stable.V1.Add_solved_work
              ( One_or_two.map res.spec.instances ~f:Single.Spec.statement
              , { proof= res.proofs
                ; fee= {fee= res.spec.fee; prover= res.prover} } ))
         ~sender:Envelope.Sender.Local)
end

include Make (Transition_frontier)

let%test_module "random set test" =
  ( module struct
    open Coda_base

    let trust_system = Mocks.trust_system

    let logger = Logger.null ()

    module Mock_snark_pool = Make (Mocks.Transition_frontier)
    open Ledger_proof.For_tests

    let apply_diff resource_pool work
        ?(proof = One_or_two.map ~f:mk_dummy_proof)
        ?(sender = Envelope.Sender.Local) fee =
      let diff =
        Mock_snark_pool.Resource_pool.Diff.Stable.Latest.Add_solved_work
          (work, {Priced_proof.Stable.Latest.proof= proof work; fee})
      in
      Mock_snark_pool.Resource_pool.Diff.apply resource_pool
        {Envelope.Incoming.data= diff; sender}

    let config verifier =
      Mock_snark_pool.Resource_pool.make_config ~verifier ~trust_system

    let gen =
      let open Quickcheck.Generator.Let_syntax in
      let gen_entry =
        Quickcheck.Generator.tuple2 Mocks.Transaction_snark_work.Statement.gen
          Fee_with_prover.gen
      in
      let%map sample_solved_work = Quickcheck.Generator.list gen_entry in
      (*This has to be None because otherwise (if frontier_broadcast_pipe_r is
      seeded with (0, empty-table)) add_snark function wouldn't add snarks in
      the snark pool (see work_is_referenced) until the first diff (first block)
      and there are no best tip diffs being fed into this pipe from the mock
      transition frontier*)
      let frontier_broadcast_pipe_r, _ = Broadcast_pipe.create None in
      let res =
        let open Deferred.Let_syntax in
        let%bind verifier =
          Verifier.create ~logger
            ~pids:(Child_processes.Termination.create_pid_set ())
        in
        let config = config verifier in
        let resource_pool =
          Mock_snark_pool.Resource_pool.create ~config ~logger
            ~frontier_broadcast_pipe:frontier_broadcast_pipe_r
        in
        let%map () =
          let open Deferred.Let_syntax in
          Deferred.List.iter sample_solved_work ~f:(fun (work, fee) ->
              let%map res = apply_diff resource_pool work fee in
              assert (Or_error.is_ok res) ;
              () )
        in
        resource_pool
      in
      res

    let%test_unit "Invalid proofs are not accepted" =
      let open Quickcheck.Generator.Let_syntax in
      let invalid_work_gen =
        let gen =
          let gen_entry =
            Quickcheck.Generator.tuple3
              Mocks.Transaction_snark_work.Statement.gen Fee_with_prover.gen
              Signature_lib.Public_key.Compressed.gen
          in
          let%map solved_work = Quickcheck.Generator.list gen_entry in
          List.fold ~init:[] solved_work
            ~f:(fun acc (work, fee, some_other_pk) ->
              (*Making it invalid by forging*)
              let invalid_sok_digest =
                Sok_message.(
                  digest @@ create ~prover:some_other_pk ~fee:fee.fee)
              in
              ( work
              , One_or_two.map work ~f:(fun statement ->
                    Ledger_proof.create ~statement
                      ~sok_digest:invalid_sok_digest ~proof:Proof.dummy )
              , fee
              , some_other_pk )
              :: acc )
        in
        Quickcheck.Generator.filter gen ~f:(fun ls ->
            List.for_all ls ~f:(fun (_, _, fee, mal_pk) ->
                not
                @@ Signature_lib.Public_key.Compressed.equal mal_pk fee.prover
            ) )
      in
      Quickcheck.test
        ~sexp_of:
          [%sexp_of:
            Mock_snark_pool.Resource_pool.t Deferred.t
            * ( Transaction_snark_work.Statement.t
              * Ledger_proof.t One_or_two.t
              * Fee_with_prover.t
              * Signature_lib.Public_key.Compressed.t )
              list] (Quickcheck.Generator.tuple2 gen invalid_work_gen)
        ~f:(fun (t, invalid_work_lst) ->
          Async.Thread_safe.block_on_async_exn (fun () ->
              let open Deferred.Let_syntax in
              let%bind t = t in
              let completed_works =
                Mock_snark_pool.Resource_pool.all_completed_work t
              in
              let%map () =
                Deferred.List.iter invalid_work_lst
                  ~f:(fun (statements, proofs, fee, _) ->
                    let%map res =
                      apply_diff t statements ~proof:(fun _ -> proofs) fee
                    in
                    assert (Or_error.is_error res) ;
                    () )
              in
              [%test_eq: Transaction_snark_work.Info.t list] completed_works
                (Mock_snark_pool.Resource_pool.all_completed_work t) ) )

    let%test_unit "When two priced proofs of the same work are inserted into \
                   the snark pool, the fee of the work is at most the minimum \
                   of those fees" =
      Quickcheck.test
        ~sexp_of:
          [%sexp_of:
            Mock_snark_pool.Resource_pool.t Deferred.t
            * Mocks.Transaction_snark_work.Statement.t
            * Fee_with_prover.t
            * Fee_with_prover.t]
        (Async.Quickcheck.Generator.tuple4 gen
           Mocks.Transaction_snark_work.Statement.gen Fee_with_prover.gen
           Fee_with_prover.gen) ~f:(fun (t, work, fee_1, fee_2) ->
          Async.Thread_safe.block_on_async_exn (fun () ->
              let%bind t = t in
              let%bind _ = apply_diff t work fee_1 in
              let%map _ = apply_diff t work fee_2 in
              let fee_upper_bound = Currency.Fee.min fee_1.fee fee_2.fee in
              let {Priced_proof.fee= {fee; _}; _} =
                Option.value_exn
                  (Mock_snark_pool.Resource_pool.request_proof t work)
              in
              assert (fee <= fee_upper_bound) ) )

    let%test_unit "A priced proof of a work will replace an existing priced \
                   proof of the same work only if it's fee is smaller than \
                   the existing priced proof" =
      Quickcheck.test
        ~sexp_of:
          [%sexp_of:
            Mock_snark_pool.Resource_pool.t Deferred.t
            * Mocks.Transaction_snark_work.Statement.t
            * Fee_with_prover.t
            * Fee_with_prover.t]
        (Quickcheck.Generator.tuple4 gen
           Mocks.Transaction_snark_work.Statement.gen Fee_with_prover.gen
           Fee_with_prover.gen) ~f:(fun (t, work, fee_1, fee_2) ->
          Async.Thread_safe.block_on_async_exn (fun () ->
              let%bind t = t in
              Mock_snark_pool.Resource_pool.remove_solved_work t work ;
              let expensive_fee = max fee_1 fee_2
              and cheap_fee = min fee_1 fee_2 in
              let%bind _ = apply_diff t work cheap_fee in
              let%map res = apply_diff t work expensive_fee in
              assert (Or_error.is_error res) ;
              assert (
                cheap_fee.fee
                = (Option.value_exn
                     (Mock_snark_pool.Resource_pool.request_proof t work))
                    .fee
                    .fee ) ) )

    let fake_work =
      `One
        (Quickcheck.random_value ~seed:(`Deterministic "worktest")
           Transaction_snark.Statement.gen)

    let%test_unit "Work that gets fed into apply_and_broadcast will be \
                   received in the pool's reader" =
      Async.Thread_safe.block_on_async_exn (fun () ->
          let pool_reader, _pool_writer = Linear_pipe.create () in
          let frontier_broadcast_pipe_r, _ =
            Broadcast_pipe.create (Some (Mocks.Transition_frontier.create ()))
          in
          let%bind verifier =
            Verifier.create ~logger
              ~pids:(Child_processes.Termination.create_pid_set ())
          in
          let config = config verifier in
          let network_pool =
            Mock_snark_pool.create ~config ~incoming_diffs:pool_reader ~logger
              ~frontier_broadcast_pipe:frontier_broadcast_pipe_r
          in
          let priced_proof =
            { Priced_proof.proof=
                `One
                  (mk_dummy_proof
                     (Quickcheck.random_value
                        ~seed:(`Deterministic "test proof")
                        Transaction_snark.Statement.gen))
            ; fee=
                { fee= Currency.Fee.of_int 0
                ; prover= Signature_lib.Public_key.Compressed.empty } }
          in
          let command =
            Mock_snark_pool.Resource_pool.Diff.Stable.V1.Add_solved_work
              (fake_work, priced_proof)
          in
          don't_wait_for
          @@ Linear_pipe.iter (Mock_snark_pool.broadcasts network_pool)
               ~f:(fun _ ->
                 let pool = Mock_snark_pool.resource_pool network_pool in
                 ( match
                     Mock_snark_pool.Resource_pool.request_proof pool fake_work
                   with
                 | Some {proof; fee= _} ->
                     assert (proof = priced_proof.proof)
                 | None ->
                     failwith "There should have been a proof here" ) ;
                 Deferred.unit ) ;
          Mock_snark_pool.apply_and_broadcast network_pool
            (Envelope.Incoming.local command) )

    let%test_unit "when creating a network, the incoming diffs in reader pipe \
                   will automatically get process" =
      Async.Thread_safe.block_on_async_exn (fun () ->
          let works =
            Quickcheck.random_sequence ~seed:(`Deterministic "works")
              Transaction_snark.Statement.gen
            |> Fn.flip Sequence.take 10
            |> Sequence.map ~f:(fun x -> `One x)
            |> Sequence.to_list
          in
          let verify_unsolved_work () =
            let work_diffs =
              List.map works ~f:(fun work ->
                  Envelope.Incoming.local
                    (Mock_snark_pool.Resource_pool.Diff.Stable.V1
                     .Add_solved_work
                       ( work
                       , Priced_proof.
                           { proof= One_or_two.map ~f:mk_dummy_proof work
                           ; fee=
                               { fee= Currency.Fee.of_int 0
                               ; prover=
                                   Signature_lib.Public_key.Compressed.empty }
                           } )) )
              |> Linear_pipe.of_list
            in
            let frontier_broadcast_pipe_r, _ =
              Broadcast_pipe.create
                (Some (Mocks.Transition_frontier.create ()))
            in
            let%bind verifier =
              Verifier.create ~logger
                ~pids:(Child_processes.Termination.create_pid_set ())
            in
            let config = config verifier in
            let network_pool =
              Mock_snark_pool.create ~logger ~config ~incoming_diffs:work_diffs
                ~frontier_broadcast_pipe:frontier_broadcast_pipe_r
            in
            don't_wait_for
            @@ Linear_pipe.iter (Mock_snark_pool.broadcasts network_pool)
                 ~f:(fun work_command ->
                   let work =
                     match work_command with
                     | Mock_snark_pool.Resource_pool.Diff.Stable.V1
                       .Add_solved_work (work, _) ->
                         work
                   in
                   assert (List.mem works work ~equal:( = )) ;
                   Deferred.unit ) ;
            Deferred.unit
          in
          verify_unsolved_work () )

    let%test_unit "rebroadcast behavior" =
      let pool_reader, _pool_writer = Linear_pipe.create () in
      let frontier_broadcast_pipe_r, _w = Broadcast_pipe.create None in
      let stmt1, stmt2 =
        Quickcheck.random_value ~seed:(`Deterministic "")
          (Quickcheck.Generator.filter
             ~f:(fun (a, b) ->
               Mocks.Transaction_snark_work.Statement.compare a b <> 0 )
             (Quickcheck.Generator.tuple2
                Mocks.Transaction_snark_work.Statement.gen
                Mocks.Transaction_snark_work.Statement.gen))
      in
      let fee1, fee2 =
        Quickcheck.random_value ~seed:(`Deterministic "")
          (Quickcheck.Generator.tuple2 Fee_with_prover.gen Fee_with_prover.gen)
      in
      let fake_sender =
        Envelope.Sender.Remote (Unix.Inet_addr.of_string "1.2.4.8")
      in
      Async.Thread_safe.block_on_async_exn (fun () ->
          let open Deferred.Let_syntax in
          let%bind verifier =
            Verifier.create ~logger
              ~pids:(Child_processes.Termination.create_pid_set ())
          in
          let config = config verifier in
          let network_pool =
            Mock_snark_pool.create ~logger:(Logger.null ()) ~config
              ~incoming_diffs:pool_reader
              ~frontier_broadcast_pipe:frontier_broadcast_pipe_r
          in
          let resource_pool = Mock_snark_pool.resource_pool network_pool in
          let%bind res1 =
            apply_diff ~sender:fake_sender resource_pool stmt1 fee1
          in
          Or_error.ok_exn res1 |> ignore ;
          let rebroadcastable1 =
            Mock_snark_pool.For_tests.get_rebroadcastable resource_pool
              ~is_expired:(Fn.const `Ok)
          in
          [%test_eq: Mock_snark_pool.Resource_pool.Diff.t list]
            rebroadcastable1 [] ;
          let%bind res2 = apply_diff resource_pool stmt2 fee2 in
          let proof2 = One_or_two.map ~f:mk_dummy_proof stmt2 in
          Or_error.ok_exn res2 |> ignore ;
          let rebroadcastable2 =
            Mock_snark_pool.For_tests.get_rebroadcastable resource_pool
              ~is_expired:(Fn.const `Ok)
          in
          [%test_eq: Mock_snark_pool.Resource_pool.Diff.t list]
            rebroadcastable2
            [Add_solved_work (stmt2, {proof= proof2; fee= fee2})] ;
          let rebroadcastable3 =
            Mock_snark_pool.For_tests.get_rebroadcastable resource_pool
              ~is_expired:(Fn.const `Expired)
          in
          [%test_eq: Mock_snark_pool.Resource_pool.Diff.t list]
            rebroadcastable3 [] ;
          Deferred.unit )
  end )
