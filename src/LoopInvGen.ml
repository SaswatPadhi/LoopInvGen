open Core
open SyGuS
open Types
open Utils
open VPIE

type 'a config = {
  for_VPIE : 'a VPIE.config ;

  base_random_seed : string ;
  max_restarts : int ;
  max_steps_on_restart : int ;
  model_completion_mode : [ `RandomGeneration | `UsingZ3 ] ;
}

let default_config = {
  for_VPIE = {
    VPIE.default_config with
      simplify = false ;
  } ;

  base_random_seed = "LoopInvGen" ;
  max_restarts = 64 ;
  max_steps_on_restart = 32 ;
  model_completion_mode = `RandomGeneration ;
}

(*let satisfyPost ?(conf = default_config) ~(states : value list list)
                ~(z3 : ZProc.t) ~(sygus : SyGuS.t) (inv : PIE.desc) : PIE.desc =
  Log.debug (lazy ("POST >> Strengthening against postcondition:"
                  ^ Log.indented_sep ^ inv)) ;
  ZProc.create_local z3 ~db:[ "(assert " ^ inv ^ ")" ] ;
  let pre_inv = VPIE.learnVPreCond ~conf:conf.for_VPIE ~consts:sygus.consts ~z3
    ((PIE.create_pos_job ()
        ~f: (ZProc.constraint_sat_function ("(not " ^ inv ^ ")")
              ~z3 ~arg_names:(List.map sygus.state_vars ~f:fst))
        ~args: sygus.state_vars
        ~post: (fun _ res -> match res with
                            | Ok v when v = vfalse -> true
                            | _ -> false)
        ~pos_tests: states
     ), sygus.post.expr)
  in ZProc.close_local z3
   ; Log.debug (lazy ("POST Delta: " ^ pre_inv))
   ; ZProc.simplify z3 ("(and " ^ pre_inv ^ " " ^ inv ^ ")")*)

let satisfyTrans ?(conf = default_config) ~(sygus : SyGuS.t) ~(z3 : ZProc.t)
                 ~(states : value list list) (inv : PIE.desc) : PIE.desc =
  let invf_call =
       "(invf " ^ (List.to_string_map sygus.inv_vars ~sep:" " ~f:fst) ^ ")" in
  let invf'_call =
    "(invf " ^ (List.to_string_map sygus.inv_vars ~sep:" "
                  ~f:(fun (s, _) -> s ^ "!")) ^ ")" in
  let trans_desc = ZProc.simplify z3 sygus.trans.expr in
  let eval_term = (if not (conf.model_completion_mode = `UsingZ3) then "true"
                   else "(and " ^ invf_call ^ " " ^ trans_desc ^ ")") in
  let rec helper inv =
  begin
    Log.debug (lazy ("IND >> Strengthening for inductiveness:"
                    ^ Log.indented_sep ^ inv)) ;
    if inv = "false" then inv else
    let inv_def =
      "(define-fun invf (" ^
      (List.to_string_map sygus.inv_vars ~sep:" "
                          ~f:(fun (s, t) -> "(" ^ s ^ " " ^
                                            (Types.string_of_typ t) ^ ")")) ^
      ") Bool " ^ inv ^ ")"
    in ZProc.create_local z3 ~db:[ inv_def ; "(assert " ^ trans_desc ^ ")"
                                           ; "(assert " ^ invf_call ^ ")" ]
     ; let pre_inv =
         VPIE.learnVPreCond
           ~conf:conf.for_VPIE ~consts:sygus.consts ~z3 ~eval_term
           ((PIE.create_pos_job ()
               ~f:(ZProc.constraint_sat_function ("(not " ^ invf'_call ^ ")")
                     ~z3 ~arg_names:(List.map sygus.state_vars ~f:fst))
               ~args: sygus.state_vars
               ~post: (fun _ res -> match res with
                                    | Ok v when v = vfalse -> true
                                    | _ -> false)
               ~pos_tests: states
            ), invf'_call)
      in ZProc.close_local z3
       ; Log.debug (lazy ("IND Delta: " ^ pre_inv))
       ; if pre_inv = "true" then inv
         else helper (ZProc.simplify z3 ("(and " ^ pre_inv ^ " " ^ inv ^ ")"))
  end in helper inv

let counterPre ?(seed = default_config.base_random_seed)
               ?(avoid_roots = []) (inv : PIE.desc) ~(sygus : SyGuS.t)
               ~(z3 : ZProc.t) : value list option =
  Log.debug (lazy ("PRE >> Checking if weaker than precond:"
                  ^ Log.indented_sep ^ inv)) ;
  let open Quickcheck in
  random_value ~size:1 ~seed:(`Deterministic seed)
    (Simulator.gen_state_from_model sygus z3
       (ZProc.implication_counter_example z3 sygus.pre.expr inv
         ~db:(if avoid_roots = [] then []
               else [ "(assert (and " ^ (String.concat avoid_roots ~sep:" ")
                   ^ "))" ])))

let rec learnInvariant_internal ?(avoid_roots = []) ?(conf = default_config)
                                ~(states : value list list) (sygus : SyGuS.t)
                                (restarts_left : int) (seed : string)
                                (z3 : ZProc.t) : PIE.desc =
  let restart_with_counter model =
    if restarts_left < 1 then "false" else
      let open Quickcheck
      in learnInvariant_internal
          ~avoid_roots:(List.cons_opt_value
            (Simulator.build_avoid_constraints sygus model) avoid_roots)
          ~states:(List.dedup (
              states @ (random_value ~size:conf.max_steps_on_restart
                                     ~seed:(`Deterministic seed)
                                     (Simulator.simulate_from sygus z3 model))))
          ~conf sygus (restarts_left - 1) (seed ^ "#") z3
  in let inv = satisfyTrans ~conf ~sygus ~states ~z3 (sygus.post.expr)
  in match counterPre ~seed ~avoid_roots ~sygus ~z3 inv with
     | (Some _) as model -> restart_with_counter model
     | None -> inv

let learnInvariant ?(avoid_roots = []) ?(conf = default_config)
                   ~(states : value list list) ~(zpath : string)
                   (sygus : SyGuS.t) : PIE.desc =
  let open ZProc
  in process ~zpath (fun z3 ->
       Simulator.setup sygus z3 ;
       if not ((implication_counter_example z3 sygus.pre.expr sygus.post.expr)
               = None) then "false"
       else learnInvariant_internal ~avoid_roots ~conf ~states sygus
                                    conf.max_restarts conf.base_random_seed z3)