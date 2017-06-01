open Core
open Core.Unix
open Exceptions
open Sexplib.Sexp
open SyGuS
open GenTests
open Types

let setup (s : sygus) (z3 : ZProc.t) : unit =
  ignore (ZProc.run_queries ~local:false z3 ~db:(
    ("(set-logic " ^ s.logic ^ ")") ::
    (List.map ~f:(fun (v, t) -> ("(declare-var " ^ v ^ " " ^ (string_of_typ t) ^ ")"))
              (s.state_vars @ s.trans_vars))) [])

let filter_state ?trans:(trans=true) (model : (string * Types.value) list)
                 : (string * Types.value) list =
  if trans then List.filter_map model ~f:(fun (n, v) -> match String.chop_suffix n "!" with
                                                        | None -> None
                                                        | Some n -> Some (n, v))
  else List.filter model ~f:(fun (n, _) -> String.suffix n 1 <> "!")

let transition (s : sygus) (z3 : ZProc.t) (vals : value list) : value list option =
  let results = ZProc.run_queries z3 ~db:(
    (* assert the transition *)
    ("(assert " ^ (Sexp.to_string_hum s.trans.sexp) ^ ")") ::
    (* assert all known values *)
    (List.map2_exn ~f:(fun d (v,_) -> ("(assert (= " ^ v ^ " " ^ (serialize_value d) ^ "))"))
                   vals s.state_vars)
  ) ZProc.query_for_model
  in let open List in
     match ZProc.z3_result_to_values results with
     | None -> None
     | Some model
       -> let model = filter_state ~trans:true model
          in Some (map2_exn s.state_vars vals
                            ~f:(fun (var,_) v ->
                                  Option.value (Assoc.find model var ~equal:(fun a b -> a = b))
                                               ~default: v))

let pre_state_gen (s : sygus) (z3 : ZProc.t) : value list Quickcheck.Generator.t =
  let results =
    ZProc.run_queries z3
                      ~db:["(assert " ^ (Sexp.to_string_hum s.pre.sexp) ^ ")"]
                      ZProc.query_for_model
  in let open List in
     match ZProc.z3_result_to_values results with
     | None -> raise (False_Pre_Exn (Sexp.to_string_hum s.pre.sexp))
     | Some m
       -> let model = filter ~f:(fun (v,_) -> mem ~equal:(=) s.pre.args v) m in
          let open Quickcheck.Generator
          in create(fun ~size random ->
                      List.map s.state_vars
                               ~f:(fun (v,t) -> match findi ~f:(fun _ (x,_) -> x = v) model with
                                                | None -> generate (typ_gen t) ~size random
                                                | Some (_,(_,d)) -> d))

let simulate_from (s : sygus) (z3 : ZProc.t) (root : value list)
                  : value list list Quickcheck.Generator.t =
  let open Quickcheck.Generator in
  let rec step root ~size random =
    match size with
    | 0 -> []
    | n -> match transition s z3 root with
           | None -> Log.debug (lazy (" . " ^ (state_to_string s root))) ; [root]
           | Some next -> Log.debug (lazy (" > " ^ (state_to_string s root)))
                        ; root :: (step next ~size:(n-1) random)
  in Log.debug (lazy ("New execution: "))
   ; create (step root)

let simulate (s : sygus) (z3 : ZProc.t) : value list list Quickcheck.Generator.t =
  let open Quickcheck.Generator in
    (* Picking a random state, and then checking pre:
        (typ_list_gen (List.map ~f:snd (s.state_vars)) (fun l -> s.pre.func l = VBool true))
      is pretty inefficient. *)
    (pre_state_gen s z3) >>= (simulate_from s z3)

let run ~size ~seed (s : sygus) : value list list =
  let z3 = ZProc.create ()
  in setup s z3
   ; let tests = Quickcheck.random_value ~size ~seed (simulate s z3)
     in ZProc.close z3 ; tests