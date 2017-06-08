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

let gen_state_from_model (m : ZProc.model option) (s : SyGuS.t) (z3 : ZProc.t)
                         : value list option Quickcheck.Generator.t =
  let open Quickcheck.Generator in
  match m with None -> singleton None
  | Some m
    -> create (fun ~size rnd -> Some (
            List.map s.state_vars
                    ~f:(fun (v, t) ->
                          match List.findi ~f:(fun _ (x, _) -> x = v) m
                          with None -> generate (GenTests.typ_gen t) ~size rnd
                              | Some (_, (_, d)) -> d)))

let gen_pre_state ?(avoid = []) ?(use_trans = false) (s : SyGuS.t)
                  (z3 : ZProc.t) : value list option Quickcheck.Generator.t =
  let open Quickcheck.Generator in
  match ZProc.sat_model_for_asserts z3
          ~db:[ "(assert (and " ^ s.pre.expr ^ " "
              ^ (if use_trans then s.trans.expr else "true") ^ " "
              ^ (String.concat avoid ~sep:" ") ^ "))" ]
  with None -> singleton None
     | model -> gen_state_from_model model s z3

let simulate_from (s : SyGuS.t) (z3 : ZProc.t) (root : value list option)
                  : value list list Quickcheck.Generator.t =
  let open Quickcheck.Generator in
  match root with None -> singleton []
  | Some root ->
      let step root ~size random =
        Log.debug (lazy (" > " ^ (Types.serialize_values root))) ;
        let rec step_internal root size =
          root :: (match size with
                  | 0 -> []
                  | n -> begin match transition s z3 root with
                          | None -> []
                          | Some next -> step_internal next (n-1)
                        end)
        in step_internal root size
      in Log.debug (lazy ("New execution: ")) ; create (step root)

let update_avoid_root_constraints new_root avoid s =
  match new_root with
  | None -> avoid
  | Some vals -> (SyGuS.value_assignment_constraint s.state_vars vals
                    ~negate:true) :: avoid

let run ?(avoid = []) ~size ~seed (s : SyGuS.t)
        : string list * value list list =
  ZProc.process ~init_options: [
    (* "(set-option :smt.arith.random_initial_value true)" *)
  ] (fun z3 ->
       setup s z3 ;
       let iter_size = size / 2 in
       let rec helper avoid accum =
         let open Quickcheck in
         let head_1 = random_value (gen_pre_state ~avoid s z3) ~seed ~size:1 in
         let states_1 = random_value ~size:iter_size ~seed
                          (simulate_from s z3 head_1) in
         let avoid = update_avoid_root_constraints head_1 avoid s in
         let head_2 = random_value (gen_pre_state ~avoid ~use_trans:true s z3)
                                   ~seed ~size:1 in
         let states_2 = random_value ~size:iter_size ~seed
                          (simulate_from s z3 head_2) in
         let avoid = update_avoid_root_constraints head_2 avoid s in
         let states = states_1 @ states_2
         in (if states = [] then (avoid, accum)
             else let accum = states @ accum
                  in (if List.length accum >= size then (avoid, accum)
                      else helper avoid accum))
       in helper avoid [])