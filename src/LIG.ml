open Core_kernel

open SyGuS
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
    VPIE.default_config with simplify = false ;
  } ;

  base_random_seed = "LoopInvGen" ;
  max_restarts = 64 ;
  max_steps_on_restart = 256 ;
  model_completion_mode = `RandomGeneration ;
}

let satisfyTrans ?(conf = default_config) ~(sygus : SyGuS.t) ~(z3 : ZProc.t)
                 ~(states : Value.t list list) (inv : Job.desc)
                 : (Job.desc * ZProc.model option) =
  let invf_call =
       "(invf " ^ (List.to_string_map sygus.inv_func.args ~sep:" " ~f:fst) ^ ")" in
  let invf'_call =
    "(invf " ^ (List.to_string_map sygus.inv_func.args ~sep:" "
                  ~f:(fun (s, _) -> s ^ "!")) ^ ")" in
  let eval_term = (if not (conf.model_completion_mode = `UsingZ3) then "true"
                   else "(and " ^ invf_call ^ " " ^ sygus.trans_func.expr ^ ")") in
  let rec helper inv =
  begin
    Log.info (lazy ("IND >> Strengthening for inductiveness:"
                   ^ (Log.indented_sep 4) ^ inv)) ;
    if String.equal inv "false" then ("false", None) else
    let inv_def = "(define-fun invf ("
                ^ (List.to_string_map sygus.inv_func.args ~sep:" "
                                      ~f:(fun (s, t) -> "(" ^ s ^ " " ^ (Type.to_string t) ^ ")"))
                ^ ") Bool " ^ inv ^ ")"
    in ZProc.create_scope z3 ~db:[ inv_def ; "(assert " ^ sygus.trans_func.expr ^ ")"
                                           ; "(assert " ^ invf_call ^ ")" ]
     ; let pre_inv =
         VPIE.learnVPreCond
           ~conf:conf.for_VPIE ~consts:sygus.constants ~eval_term ~post_desc:invf'_call ~z3
           (Job.create_positive states
              ~f:(ZProc.constraint_sat_function ("(not " ^ invf'_call ^ ")")
                    ~z3 ~arg_names:(List.map sygus.synth_variables ~f:fst))
              ~args: sygus.synth_variables
              ~post: (fun _ res -> match res with
                                   | Ok v when v = Value.Bool false -> true
                                   | _ -> false))
      in ZProc.close_scope z3
       ; Log.debug (lazy ("IND Delta: " ^ pre_inv))
       ; if String.equal pre_inv "true" then (inv, None)
         else begin
           let new_inv = "(and " ^ pre_inv ^ " " ^ inv ^ ")"
            in Log.info (lazy ("PRE >> Checking if the following candidate is weaker than precond:"
                        ^ (Log.indented_sep 4) ^ new_inv)) ;
               let ce = (ZProc.implication_counter_example z3 sygus.pre_func.expr new_inv)
               in if ce = None then helper new_inv else (new_inv, ce)
         end
  end in helper inv

let rec learnInvariant_internal ?(conf = default_config) (restarts_left : int)
                                ~(states : Value.t list list) (sygus : SyGuS.t)
                                (seed_string : string) (z3 : ZProc.t) : Job.desc =
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
        ~states:List.(dedup_and_sort ~compare:(compare Value.compare) (
          states @ (random_value ~size:conf.max_steps_on_restart ~seed:(`Deterministic seed_string)
                                 (simulate_from sygus z3 head))))
        ~conf (restarts_left - 1) sygus (seed_string ^ "#") z3
    end
  in match satisfyTrans ~conf ~sygus ~states ~z3 (sygus.post_func.expr) with
     | inv, None
       -> if inv <> "false" then ZProc.simplify z3 inv
          else restart_with_new_states (random_value ~seed:(`Deterministic seed_string)
                                                     (gen_pre_state ~use_trans:true sygus z3))
     | _, (Some ce_model)
       -> restart_with_new_states (random_value ~seed:(`Deterministic seed_string)
                                                (gen_state_from_model sygus (Some ce_model)))

let learnInvariant ?(conf = default_config) ~(states : Value.t list list)
                   ~(zpath : string) (sygus : SyGuS.t) : Job.desc =
  let open ZProc
  in process ~zpath
       ~random_seed:(Some (Int.to_string (Quickcheck.(random_value ~seed:(`Deterministic conf.base_random_seed)
                                                                   (Generator.small_non_negative_int)))))
       (fun z3 -> Simulator.setup sygus z3
                ; if not ((implication_counter_example z3 sygus.pre_func.expr sygus.post_func.expr) = None) then "false"
                  else learnInvariant_internal ~conf ~states conf.max_restarts sygus conf.base_random_seed z3)