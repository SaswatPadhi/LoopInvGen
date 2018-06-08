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
  user_functions: (string * string) list ;
}

let default_config = {
  for_VPIE = {
    VPIE.default_config with simplify = false ;
  } ;

  base_random_seed = "LoopInvGen" ;
  max_restarts = 64 ;
  max_steps_on_restart = 256 ;
  model_completion_mode = `RandomGeneration ;
  user_functions = [] ;
}

(*let satisfyPost ?(conf = default_config) ~(states : value list list)
                ~(z3 : ZProc.t) ~(sygus : SyGuS.t) (inv : PIE.desc) : PIE.desc =
  Log.debug (lazy ("POST >> Strengthening against postcondition:"
                  ^ Log.indented_sep ^ inv)) ;
  ZProc.create_scope z3 ~db:[ "(assert " ^ inv ^ ")" ] ;
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
  in ZProc.close_scope z3
   ; Log.debug (lazy ("POST Delta: " ^ pre_inv))
   ; ZProc.simplify z3 ("(and " ^ pre_inv ^ " " ^ inv ^ ")")*)

let satisfyTrans ?(conf = default_config) ~(sygus : SyGuS.t) ~(z3 : ZProc.t)
                 ~(states : value list list) (inv : PIE.desc)
                 : (PIE.desc * ZProc.model option) =
  let invf_call =
       "(invf " ^ (List.to_string_map sygus.inv_vars ~sep:" " ~f:fst) ^ ")" in
  let invf'_call =
    "(invf " ^ (List.to_string_map sygus.inv_vars ~sep:" "
                  ~f:(fun (s, _) -> s ^ "!")) ^ ")" in
  let eval_term = (if not (conf.model_completion_mode = `UsingZ3) then "true"
                   else "(and " ^ invf_call ^ " " ^ sygus.trans.expr ^ ")") in
  let rec helper inv =
  begin
    Log.debug (lazy ("IND >> Strengthening for inductiveness:"
                    ^ (Log.indented_sep 4) ^ inv)) ;
    if inv = "false" then ("false", None)else
    let all_state_vars =
      (List.to_string_map sygus.state_vars ~sep:" " ~f:(fun (s, _) -> s))
    in let inv_def =
      "(define-fun invf (" ^
      (List.to_string_map sygus.inv_vars ~sep:" "
                          ~f:(fun (s, t) -> "(" ^ s ^ " " ^
                                            (Types.string_of_typ t) ^ ")")) ^
      ") Bool " ^ inv ^ ")"
    in ZProc.create_scope z3 ~db:[ inv_def ; "(assert " ^ sygus.trans.expr ^ ")"
                                           ; "(assert " ^ invf_call ^ ")" ; ]
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
               ~features: (List.map ~f:(fun (_, name)
                                          -> ((ZProc.build_feature name z3),
                                              ("(" ^ name ^ " " ^ all_state_vars ^ ")")))
                                    conf.user_functions)
            ), invf'_call)
      in ZProc.close_scope z3
       ; Log.debug (lazy ("IND Delta: " ^ pre_inv))
       ; if pre_inv = "true" then (inv, None)
         else begin
           let new_inv = "(and " ^ pre_inv ^ " " ^ inv ^ ")"
            in Log.debug (lazy ("PRE >> Checking if the following candidate is weaker than precond:"
                         ^ (Log.indented_sep 4) ^ new_inv)) ;
               let ce = (ZProc.implication_counter_example z3 sygus.pre.expr new_inv)
               in if ce = None then helper new_inv else (new_inv, ce)
         end
  end in helper inv

let rec learnInvariant_internal ?(conf = default_config) (restarts_left : int)
                                ~(states : value list list) (sygus : SyGuS.t)
                                (seed_string : string) (z3 : ZProc.t) : PIE.desc =
  let open Quickcheck in
  let open Simulator in
  let restart_with_new_states head =
    if restarts_left < 1
    then (Log.error (lazy ("Reached MAX (" ^ (string_of_int conf.max_restarts)
                          ^ ") restarts. Giving up ..."))
         ; "false")
    else begin
      Log.warn (lazy ("Restarting inference engine. Attempt "
                     ^ (string_of_int (1 + conf.max_restarts - restarts_left))
                     ^ "/" ^ (string_of_int conf.max_restarts) ^".")) ;
      learnInvariant_internal
        ~states:List.(dedup_and_sort ~compare:(compare value_compare) (
          states @ (random_value ~size:conf.max_steps_on_restart ~seed:(`Deterministic seed_string)
                                 (simulate_from sygus z3 head))))
        ~conf (restarts_left - 1) sygus (seed_string ^ "#") z3
    end
  in match satisfyTrans ~conf ~sygus ~states ~z3 (sygus.post.expr) with
     | inv, None
       -> if inv <> "false" then ZProc.simplify z3 inv
          else restart_with_new_states (random_value ~seed:(`Deterministic seed_string)
                                                     (gen_pre_state ~use_trans:true sygus z3))
     | inv, (Some ce_model)
       -> restart_with_new_states (random_value ~seed:(`Deterministic seed_string)
                                                (gen_state_from_model sygus z3 (Some ce_model)))

let learnInvariant ?(conf = default_config) ~(states : value list list)
                   ~(zpath : string) (sygus : SyGuS.t) : PIE.desc =
  let open ZProc
  in process ~zpath
       ~random_seed:(Some (string_of_int (
         Quickcheck.(random_value ~seed:(`Deterministic conf.base_random_seed)
                                  (Generator.small_non_negative_int)))))
       (fun z3 ->
         Simulator.setup sygus z3 ~user_fs:(List.map ~f:(fun (a, b) -> a) conf.user_functions) ;
         if not ((implication_counter_example z3 sygus.pre.expr sygus.post.expr)
                 = None) then "false"
         else learnInvariant_internal ~conf ~states conf.max_restarts sygus
                                      conf.base_random_seed z3)
