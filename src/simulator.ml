open Core
open Core.Unix
open Exceptions
open Sexplib.Sexp
open Sygus
open Test_gen
open Types

let setup (s : sygus) (z3 : Zproc.proc_info) : unit =
  ignore (Zproc.run_queries ~local:false z3 (
    ("(set-logic " ^ s.logic ^ ")") ::
    (List.map ~f:(fun (v, t) -> ("(declare-var " ^ v ^ " " ^ (string_of_typ t) ^ ")"))
              (s.state_vars @ s.trans_vars))) [])

let filter_state ?trans:(trans=true) (model : (string * Types.value) list)
                 : (string * Types.value) list =
  if trans then List.filter_map model ~f:(fun (n, v) -> match String.chop_suffix n "!" with
                                                        | None -> None
                                                        | Some n -> Some (n, v))
  else List.filter model ~f:(fun (n, _) -> String.suffix n 1 <> "!")

let transition (s : sygus) (z3 : Zproc.proc_info) (vals : value list) : value list option =
  let results = Zproc.run_queries z3 (
    (* assert the transition *)
    ("(assert " ^ (Sexp.to_string_hum s.trans.sexp) ^ ")") ::
    (* assert all known values *)
    (List.map2_exn ~f:(fun v (var,_) -> ("(assert (= " ^ var ^ " "
                                        ^ (serialize_value v) ^ "))"))
                   vals s.state_vars)
  ) ["(check-sat)" ; "(get-model)"]
  in let open List in
     if hd_exn results = "unsat" then None
     else Some (
       let model = filter_state (Zproc.z3_result_to_values (hd_exn (tl_exn results)))
       in map2_exn s.state_vars vals
                   ~f:(fun (var,_) v -> match Assoc.find model var ~equal:(fun a b -> a = b)
                                        with None -> v | Some v' -> v'))

let pre_state_gen (s : sygus) (z3 : Zproc.proc_info) : value list Quickcheck.Generator.t =
  let results = Zproc.run_queries z3
                                  ["(assert " ^ (Sexp.to_string_hum s.pre.sexp) ^ ")"]
                                  ["(check-sat)" ; "(get-model)"]
  in let open List in
     if hd_exn results = "unsat" then raise (False_Pre_Exn (Sexp.to_string_hum s.pre.sexp))
     else let model = filter_state ~trans:true
                                   (Zproc.z3_result_to_values (hd_exn (tl_exn results))) in
          let model = filter ~f:(fun (v,_) -> mem ~equal:(=) s.pre.args v) model in
          let open Quickcheck.Generator
          in create(fun ~size random ->
                      List.map s.state_vars
                              ~f:(fun (v,t) -> match findi ~f:(fun _ (x,_) -> x = v) model with
                                                | None -> generate (typ_gen t) ~size random
                                                | Some (_,(_,d)) -> d))

let simulate (s : sygus) (z3 : Zproc.proc_info) : value list list Quickcheck.Generator.t =
  let open Quickcheck.Generator in
    (* Picking a random state, and then checking pre:
         (typ_list_gen (List.map ~f:snd (s.state_vars)) (fun l -> s.pre.func l = VBool true))
       is pretty inefficient. *)
    (pre_state_gen s z3)
    >>= fun root ->
          let rec step root ~size random =
            match size with
            | 0 -> []
            | n -> begin match transition s z3 root with
                    | None -> Log.debug (lazy (" . " ^ (state_to_string s root))) ; [root]
                    | Some next -> Log.debug (lazy (" > " ^ (state_to_string s root)))
                                 ; root :: (step next ~size:(n-1) random)
                   end
          in Log.debug (lazy ("New execution: "))
           ; create (step root)

let run ~size ~seed (s : sygus) : value list list =
  let z3 = Zproc.create ()
  in setup s z3
   ; let tests = Quickcheck.random_value ~size ~seed (simulate s z3)
     in Zproc.close z3 ; tests