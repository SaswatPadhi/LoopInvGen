open Core
open Core.Unix
open Exceptions
open Sexplib.Sexp
open SyGuS
open GenTests
open Types

let setup (s : SyGuS.t) (z3 : ZProc.t) : unit =
  ignore (ZProc.run_queries ~local:false z3 ~db:(
    ("(set-logic " ^ s.logic ^ ")") ::
    (List.map ~f:(fun (v, t) -> ("(declare-var " ^ v ^ " " ^
                                 (string_of_typ t) ^ ")"))
              (s.state_vars @ s.trans_vars))) [])

let build_function (expr : string) ~(z3 : ZProc.t) ~(arg_names : string list)
                   : (value list -> value) =
  fun (values : value list) ->
    match ZProc.run_queries z3
            ~db:(("(assert " ^ expr ^ ")") ::
                (List.map2_exn arg_names values
                               ~f:(fun n v -> ("(assert (= " ^ n ^ " " ^
                                               (serialize_value v) ^ "))"))))
            [ "(check-sat)" ]
    with [ "sat" ]   -> vtrue
       | [ "unsat" ] -> vfalse
       | _ -> raise (Internal_Exn "Failed")

let filter_state ?trans:(trans=true) (model : (string * Types.value) list)
                 : (string * Types.value) list =
  if trans
  then List.filter_map model
                       ~f:(fun (n, v) -> match String.chop_suffix n "!" with
                                         | None -> None
                                         | Some n -> Some (n, v))
  else List.filter model ~f:(fun (n, _) -> String.suffix n 1 <> "!")

let transition (s : SyGuS.t) (z3 : ZProc.t) (vals : value list)
               : value list option =
  let results = ZProc.run_queries z3 ~db:(
    (* assert the transition *)
    ("(assert " ^ s.trans.expr ^ ")") ::
    (* assert all known values *)
    (List.map2_exn ~f:(fun d (v,_) -> ("(assert (= " ^ v ^ " " ^
                                       (serialize_value d) ^ "))"))
                   vals s.state_vars)
  ) (ZProc.query_for_model ())
  in let open List in
     match ZProc.z3_result_to_values results with
     | None -> None
     | Some model
       -> let model = filter_state ~trans:true model
          in Some (map2_exn s.state_vars vals
                            ~f:(fun (var,_) v ->
                                  Option.value (Assoc.find model var ~equal:(=))
                                               ~default: v))

let pre_state_gen (s : SyGuS.t) (z3 : ZProc.t)
                  : ZProc.model Quickcheck.Generator.t =
  let results = ZProc.run_queries z3 ~db:["(assert " ^ s.pre.expr ^ ")"]
                                  (ZProc.query_for_model ())
  in let open List in
     match ZProc.z3_result_to_values results with
     | None -> raise (False_Pre_Exn s.pre.expr)
     | Some model
       -> Quickcheck.Generator.singleton (
            filter model ~f:(fun (v,_) -> mem ~equal:(=) s.pre.args v))

let simulate_from (s : SyGuS.t) (z3 : ZProc.t) (root : ZProc.model)
                  : value list list Quickcheck.Generator.t =
  let open Quickcheck.Generator in
  let step root ~size random =
    let root = List.map s.state_vars
                        ~f:(fun (v, t) ->
                              match List.findi ~f:(fun _ (x,_) -> x = v) root
                              with None -> generate (typ_gen t) ~size random
                                 | Some (_,(_,d)) -> d)
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
  ZProc.process (fun z3 -> setup s z3 ;
                           Quickcheck.random_value ~size ~seed (simulate s z3))