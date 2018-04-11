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
  user_functions: (string list)*string ;
}

let default_config = {
  for_VPIE = {
    VPIE.default_config with simplify = false ;
  } ;

  base_random_seed = "LoopInvGen" ;
  max_restarts = 64 ;
  max_steps_on_restart = 256 ;
  model_completion_mode = `RandomGeneration ;
  user_functions = ([], "") ;
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
                 ~(states : value list list) (inv : PIE.desc) : PIE.desc =
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
    if inv = "false" then inv else
    let inv_def =
      "(define-fun invf (" ^
      (List.to_string_map sygus.inv_vars ~sep:" "
                          ~f:(fun (s, t) -> "(" ^ s ^ " " ^
                                            (Types.string_of_typ t) ^ ")")) ^
      ") Bool " ^ inv ^ ")"
    in ZProc.create_scope z3 ~db:[ inv_def ; "(assert " ^ sygus.trans.expr ^ ")"
                                           ; "(assert " ^ invf_call ^ ")" ; (snd conf.user_functions)]
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
      in ZProc.close_scope z3
       ; Log.debug (lazy ("IND Delta: " ^ pre_inv))
       ; if pre_inv = "true" then inv
         else helper ("(and " ^ pre_inv ^ " " ^ inv ^ ")")
  end in helper inv

let counterPre ?(seed = default_config.base_random_seed) ~(sygus : SyGuS.t)
               ~(z3 : ZProc.t) (inv : PIE.desc) : value list option =
  Log.debug (lazy ("PRE >> Checking if weaker than precond:"
                  ^ (Log.indented_sep 4) ^ inv)) ;
  let open Quickcheck in
  random_value ~size:1 ~seed:(`Deterministic seed)
    (Simulator.gen_state_from_model sygus z3
       (ZProc.implication_counter_example z3 sygus.pre.expr inv))

let rec learnInvariant_internal ?(conf = default_config) (restarts_left : int)
                                ~(states : value list list) (sygus : SyGuS.t)
                                (seed : string) (z3 : ZProc.t) : PIE.desc =
  let restart_with_counter model =
    if restarts_left < 1
    then (Log.error (lazy ("Reached MAX (" ^ (string_of_int conf.max_restarts)
                          ^ ") restarts. Giving up ..."))
         ; "false")
    else begin
      Log.warn (lazy ("Restarting inference engine. Attempt "
                     ^ (string_of_int (1 + conf.max_restarts - restarts_left))
                     ^ "/" ^ (string_of_int conf.max_restarts) ^".")) ;
      let open Quickcheck
      in learnInvariant_internal
          ~states:(List.dedup_and_sort (
              states @ (random_value ~size:conf.max_steps_on_restart
                                     ~seed:(`Deterministic seed)
                                     (Simulator.simulate_from sygus z3 model))))
          ~conf (restarts_left - 1) sygus (seed ^ "#") z3
    end
  in let inv = satisfyTrans ~conf ~sygus ~states ~z3 (sygus.post.expr)
  in match counterPre ~seed ~sygus ~z3 inv with
     | (Some _) as model -> restart_with_counter model
     | None -> ZProc.simplify z3 inv

let learnInvariant ?(conf = default_config) ~(states : value list list)
                   ~(zpath : string) (sygus : SyGuS.t) : PIE.desc =
  let open ZProc
  in process ~zpath (fun z3 ->
       Simulator.setup sygus z3 ;
       if not ((implication_counter_example z3 sygus.pre.expr sygus.post.expr)
               = None) then "false"
       else learnInvariant_internal ~conf ~states conf.max_restarts sygus
                                    conf.base_random_seed z3)