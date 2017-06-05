open Core
open Exceptions
open SyGuS
open Types

let setup (s : SyGuS.t) (z3 : ZProc.t) : unit =
  ignore (ZProc.run_queries ~local:false z3 ~db:(
    ("(set-logic " ^ s.logic ^ ")") ::
    (List.map ~f:(fun (v, t) -> ("(declare-var " ^ v ^ " " ^
                                 (string_of_typ t) ^ ")"))
              (s.state_vars @ s.trans_vars))) [])

let filter_state ?(trans = true) (model : (string * Types.value) list)
                 : (string * Types.value) list =
  if trans
  then List.filter_map model
                       ~f:(fun (n, v) -> match String.chop_suffix n "!" with
                                         | None -> None
                                         | Some n -> Some (n, v))
  else List.filter model ~f:(fun (n, _) -> String.is_suffix n ~suffix:"!")

let transition (s : SyGuS.t) (z3 : ZProc.t) (vals : value list)
               : value list option =
  match ZProc.sat_model_for_asserts z3
          ~db:[ ("(assert " ^ s.trans.expr ^ ")")
              ; ( "(assert (and "
                ^ (Utils.List.to_string_map2 ~sep:" " vals s.state_vars
                    ~f:(fun d (v, _) -> ("(= " ^ v ^ " " ^
                                         (serialize_value d) ^ ")")))
                ^ "))")]
  with None -> None
     | Some model
       -> let open List in
          let model = filter_state ~trans:true model
          in Some (map2_exn s.state_vars vals
                            ~f:(fun (var, _) v ->
                                  Option.value (Assoc.find model var ~equal:(=))
                                               ~default: v))

let pre_state_gen (s : SyGuS.t) (z3 : ZProc.t)
                  : ZProc.model Quickcheck.Generator.t =
  match ZProc.sat_model_for_asserts z3 ~db:["(assert " ^ s.pre.expr ^ ")"]
  with None -> raise (False_Pre_Exn s.pre.expr)
     | Some model
       -> Quickcheck.Generator.singleton (
            List.filter model ~f:(fun (x, _) -> List.exists s.pre.args
                                                  ~f:(fun (v, _) -> v = x)))

let simulate_from (s : SyGuS.t) (z3 : ZProc.t) (root : ZProc.model)
                  : value list list Quickcheck.Generator.t =
  let open Quickcheck.Generator in
  let step root ~size random =
    let root = List.map s.state_vars
                        ~f:(fun (v, t) ->
                              match List.findi ~f:(fun _ (x,_) -> x = v) root
                              with None -> generate (GenTests.typ_gen t) ~size random
                                 | Some (_, (_, d)) -> d)
    in Log.debug (lazy (" > " ^ (Types.serialize_values root))) ;
    let rec step_internal root size =
      root :: (match size with
              | 0 -> []
              | n -> begin match transition s z3 root with
                      | None -> []
                      | Some next -> step_internal next (n-1)
                     end)
    in step_internal root size
  in Log.debug (lazy ("New execution: ")) ; create (step root)

let simulate (s : SyGuS.t) (z3 : ZProc.t)
             : value list list Quickcheck.Generator.t =
  let open Quickcheck.Generator in
    (pre_state_gen s z3) >>= (simulate_from s z3)

let run ~size ~seed (s : SyGuS.t) : value list list =
  ZProc.process ~init_options: [
    (* "(set-option :smt.arith.random_initial_value true)" *)
  ] (fun z3 -> setup s z3
             ; Quickcheck.random_value ~size ~seed (simulate s z3))
