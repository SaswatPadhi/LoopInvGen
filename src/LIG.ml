open Core_kernel

open SyGuS
open Utils

type 'a config = {
  _VPIE : 'a VPIE.config ;

  base_random_seed : string ;
  max_restarts : int ;
  max_steps_on_restart : int ;
  model_completion_mode : [ `RandomGeneration | `UsingZ3 ] ;
}

type stats = {
  mutable lig_ce : int ;
  mutable lig_time_ms : float ;
  mutable _VPIE : VPIE.stats list ;
} [@@deriving sexp]

let default_config = {
  _VPIE = {
    VPIE.default_config with simplify = false ;
  } ;

  base_random_seed = "LoopInvGen" ;
  max_restarts = 64 ;
  max_steps_on_restart = 256 ;
  model_completion_mode = `RandomGeneration ;
}

let satisfyTrans ?(conf = default_config) ~(sygus : SyGuS.t) ~(z3 : ZProc.t)
                 ~(states : Value.t list list) (inv : Job.desc) stats
                 : Job.desc * ZProc.model option =
  let invf_call =
    "(invf " ^ (List.to_string_map sygus.inv_func.args ~sep:" " ~f:fst) ^ ")" in
  let invf'_call =
    "(invf " ^ (List.to_string_map sygus.inv_func.args ~sep:" "
                  ~f:(fun (s, _) -> s ^ "!")) ^ ")" in
  let eval_term = (if not (conf.model_completion_mode = `UsingZ3) then "true"
                   else "(and " ^ invf_call ^ " " ^ sygus.trans_func.body ^ ")") in
  let rec helper inv =
    Log.info (lazy ("IND >> Strengthening for inductiveness:"
                   ^ (Log.indented_sep 4) ^ inv)) ;
    if String.equal inv "false" then ("false", None) else
    let inv_def = "(define-fun invf ("
                ^ (List.to_string_map sygus.inv_func.args ~sep:" "
                                      ~f:(fun (s, t) -> "(" ^ s ^ " " ^ (Type.to_string t) ^ ")"))
                ^ ") Bool " ^ inv ^ ")"
    in ZProc.create_scope z3 ~db:[ inv_def ; "(assert " ^ sygus.trans_func.body ^ ")"
                                           ; "(assert " ^ invf_call ^ ")" ]
     ; let pre_inv, vpie_stats =
         VPIE.learnVPreCond ~z3 ~eval_term
           ~conf:conf._VPIE ~consts:sygus.constants ~post_desc:invf'_call
           (Job.create ()
              ~pos_tests:states
              ~f:(ZProc.constraint_sat_function ("(not " ^ invf'_call ^ ")")
                    ~z3 ~arg_names:(List.map sygus.synth_variables ~f:fst))
              ~args:sygus.synth_variables
              ~post:(fun _ res -> res = Ok (Value.Bool false)))
        in ZProc.close_scope z3
         ; Log.debug (lazy ("IND Delta: " ^ pre_inv))
         ; if String.equal pre_inv "true"
           then (inv, None)
           else (stats.lig_time_ms <- stats.lig_time_ms +. vpie_stats.vpi_time_ms
                ; stats.lig_ce <- stats.lig_ce + vpie_stats.vpi_ce
                ; stats._VPIE <- vpie_stats :: stats._VPIE
                ; let new_inv = "(and " ^ pre_inv ^ " " ^ inv ^ ")"
                   in Log.info (lazy ("PRE >> Checking if the following candidate is weaker than precond:"
                                     ^ (Log.indented_sep 4) ^ new_inv))
                    ; let ce = ZProc.implication_counter_example z3 sygus.pre_func.body new_inv
                       in if ce = None then helper new_inv else (new_inv, ce))
   in helper inv

let rec learnInvariant_internal ?(conf = default_config) (restarts_left : int)
                                ~(states : Value.t list list) (sygus : SyGuS.t)
                                (seed_string : string) (z3 : ZProc.t) stats
                                : Job.desc * stats =
  let open Quickcheck in
  let open Simulator in
  let restart_with_new_states head =
    stats.lig_ce <- stats.lig_ce + 1 ;
    if restarts_left < 1
    then (Log.error (lazy ("Reached MAX (" ^ (string_of_int conf.max_restarts)
                          ^ ") restarts. Giving up ..."))
         ; ("false", stats))
    else begin
      Log.warn (lazy ("Restarting inference engine. Attempt "
                     ^ (string_of_int (1 + conf.max_restarts - restarts_left))
                     ^ "/" ^ (string_of_int conf.max_restarts) ^".")) ;
      let new_states = random_value ~size:conf.max_steps_on_restart
                                    ~seed:(`Deterministic seed_string)
                                    (simulate_from sygus z3 head)
       in learnInvariant_internal
            ~states:List.(dedup_and_sort ~compare:(compare Value.compare)
                                         (states @ new_states))
        ~conf:{ conf with
                _VPIE = { conf._VPIE with
                          _PIE = { conf._VPIE._PIE with
                                   max_conflict_group_size = conf._VPIE._PIE.max_conflict_group_size + 4
              } } }
        (restarts_left - 1) sygus (seed_string ^ "#") z3 stats
    end
  in match (
    if sygus.post_func.expressible
    then begin
      Log.info (lazy "Starting with initial invariant = postcondition.") ;
      (None, sygus.post_func.body)
    end
    else begin
      ZProc.create_scope z3 ;
      Log.warn (lazy "Postcondition is not expressive within the provided grammar!") ;
      let inv, vpie_stats =
          VPIE.learnVPreCond
            ~z3 ~conf:conf._VPIE ~consts:sygus.constants
            ~post_desc:sygus.post_func.body
            ~eval_term:(if not (conf.model_completion_mode = `UsingZ3)
                        then "true" else sygus.post_func.body)
          (Job.create ()
              ~pos_tests:states
               ~f:(ZProc.constraint_sat_function
                     (if String.is_prefix sygus.post_func.body ~prefix:"("
                      then ("(not " ^ sygus.post_func.body ^ ")")
                      else ("(not (" ^ sygus.post_func.body ^ "))"))
                     ~z3 ~arg_names:(List.map sygus.synth_variables ~f:fst))
               ~args: sygus.synth_variables
               ~post: (fun _ res -> res = Ok (Value.Bool false)))
         in stats.lig_time_ms <- stats.lig_time_ms +. vpie_stats.vpi_time_ms
          ; stats.lig_ce <- stats.lig_ce + vpie_stats.vpi_ce
          ; stats._VPIE <- vpie_stats :: stats._VPIE
          ; ZProc.close_scope z3
          ; ((ZProc.implication_counter_example z3 sygus.pre_func.body inv), inv)
      end
  ) with Some ce, _
         -> restart_with_new_states
               (random_value ~seed:(`Deterministic seed_string)
                             (gen_state_from_model sygus (Some ce)))
       | None, inv
         -> Log.info (lazy ("Starting with the following initial invariant:"
                           ^ (Log.indented_sep 4) ^ inv))
          ; match satisfyTrans ~conf ~sygus ~states ~z3 inv stats with
            | inv, None
              -> if inv <> "false" then ((ZProc.simplify z3 inv), stats)
                  else restart_with_new_states (random_value ~seed:(`Deterministic seed_string)
                                                            (gen_pre_state ~use_trans:true sygus z3))
            | _, (Some ce_model)
              -> restart_with_new_states (random_value ~seed:(`Deterministic seed_string)
                                                        (gen_state_from_model sygus (Some ce_model)))

let learnInvariant ?(conf = default_config) ~(states : Value.t list list)
                   ~(zpath : string) (sygus : SyGuS.t) : Job.desc * stats =
  let open ZProc in
  let stats = { _VPIE = [] ; lig_time_ms = 0.0 ; lig_ce = 0 }
  in process ~zpath
       ~random_seed:(Some (Int.to_string (Quickcheck.(random_value ~seed:(`Deterministic conf.base_random_seed)
                                                                   (Generator.small_non_negative_int)))))
       (fun z3 -> Simulator.setup sygus z3
                ; if (implication_counter_example z3 sygus.pre_func.body sygus.post_func.body) <> None
                  then ("false", stats)
                  else learnInvariant_internal ~conf ~states conf.max_restarts
                                               sygus conf.base_random_seed z3 stats)
