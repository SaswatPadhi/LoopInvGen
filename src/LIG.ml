open Core_kernel

open SyGuS
open Utils

module Config = struct
  type 'a t = {
    _VPIE : 'a VPIE.Config.t ;

    base_random_seed : string ;
    max_steps_on_restart : int ;
    model_completion_mode : [ `RandomGeneration | `UsingZ3 ] ;
    user_features: (string * string) list ;
  }

  let default : 'a t = {
    _VPIE = {
      VPIE.Config.default with do_simplify = false ;
    } ;

    base_random_seed = "LoopInvGen" ;
    max_steps_on_restart = 256 ;
    model_completion_mode = `RandomGeneration ;
    user_features = [] ;
  }
end

type stats = {
  mutable lig_ce : int ;
  mutable lig_time_ms : float ;
  mutable _VPIE : VPIE.stats list ;
} [@@deriving sexp]

let satisfyTrans ?(config = Config.default) ~(sygus : SyGuS.t) ~(z3 : ZProc.t)
                 ~(states : Value.t list list) ~(neg_states : Value.t list list) (inv : Job.desc) stats
                 : Job.desc * ZProc.model option =
  let invf_call =
    "(invf " ^ (List.to_string_map sygus.inv_func.args ~sep:" " ~f:fst) ^ ")" in
  let invf'_call =
    "(invf " ^ (List.to_string_map sygus.inv_func.args ~sep:" "
                  ~f:(fun (s, _) -> s ^ "!")) ^ ")" in
  let eval_term = (if not (Poly.equal config.model_completion_mode `UsingZ3) then "true"
                   else "(and " ^ invf_call ^ " " ^ sygus.trans_func.body ^ ")") in
  let rec helper inv =
    Log.info (lazy ("IND >> Strengthening for inductiveness:"
                   ^ (Log.indented_sep 4) ^ inv)) ;
    if String.equal inv "false" then ("false", None) else
    let inv_def = "(define-fun invf ("
                ^ (List.to_string_map sygus.inv_func.args ~sep:" "
                                      ~f:(fun (s, t) -> "(" ^ s ^ " " ^ (Type.to_string t) ^ ")"))
                ^ ") Bool " ^ inv ^ ")" in
    let all_state_vars =
          (List.to_string_map sygus.synth_variables ~sep:" " ~f:(fun (s, _) -> s))
    in ZProc.create_scope z3 ~db:[ inv_def ; "(assert " ^ sygus.trans_func.body ^ ")"
                                           ; "(assert " ^ invf_call ^ ")" ]
     ; let pre_inv, vpie_stats =
         VPIE.learnVPreCond ~z3 ~eval_term
           ~config:config._VPIE ~consts:sygus.constants ~post_desc:invf'_call
           (Job.create ()
              ~pos_tests:states
              ~neg_tests:neg_states
              ~f:(ZProc.constraint_sat_function ("(not " ^ invf'_call ^ ")")
                    ~z3 ~arg_names:(List.map sygus.synth_variables ~f:fst))
              ~args:sygus.synth_variables
              ~features: (List.map ~f:(fun (_, name) -> ( (ZProc.build_feature name z3)
                                                        , ("(" ^ name ^ " " ^ all_state_vars ^ ")")))
                                   config.user_features)
              ~post:(fun _ -> function Ok (Value.Bool false) -> true | _ -> false))
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
                       in if Option.is_none ce then helper new_inv else (new_inv, ce))
   in helper inv

let rec learnInvariant_internal ?(config = Config.default)
                                ~(states : Value.t list list) ~(neg_states : Value.t list list)
                                (sygus : SyGuS.t) (seed_string : string) (z3 : ZProc.t) stats
                                : Job.desc * stats =
  let open Quickcheck in
  let open StateSampler in
  let restart_with_new_states head =
    stats.lig_ce <- stats.lig_ce + 1 ;
    Log.error (lazy ("Restarting inference engine ...")) ;
    let new_states = random_value ~size:config.max_steps_on_restart
                                  ~seed:(`Deterministic seed_string)
                                  (gen_states_from sygus z3 head)
     in learnInvariant_internal
          ~states:List.(dedup_and_sort ~compare:(compare Value.compare) (states @ new_states))
          ~neg_states
          ~config:{ config with
                    _VPIE = { config._VPIE with
                              _PIE = { config._VPIE._PIE with
                                       max_conflict_group_size = config._VPIE._PIE.max_conflict_group_size + 4
                  } } }
          sygus (seed_string ^ "#") z3 stats
  in match (
    if sygus.post_func.expressible
    then begin
      Log.info (lazy "Starting with initial invariant = postcondition.") ;
      (None, sygus.post_func.body)
    end
    else begin
      ZProc.create_scope z3 ;
      Log.info (lazy "Postcondition is not expressive within the provided grammar!") ;
      let inv, vpie_stats =
          VPIE.learnVPreCond
            ~z3 ~config:config._VPIE ~consts:sygus.constants
            ~post_desc:sygus.post_func.body
            ~eval_term:(if not (Poly.equal config.model_completion_mode `UsingZ3)
                        then "true" else sygus.post_func.body)
          (Job.create ()
              ~pos_tests:states
              ~neg_tests:neg_states
               ~f:(ZProc.constraint_sat_function
                     (if String.is_prefix sygus.post_func.body ~prefix:"("
                      then ("(not " ^ sygus.post_func.body ^ ")")
                      else ("(not (" ^ sygus.post_func.body ^ "))"))
                     ~z3 ~arg_names:(List.map sygus.synth_variables ~f:fst))
               ~args: sygus.synth_variables
               ~post:(fun _ -> function Ok (Value.Bool false) -> true | _ -> false))
         in stats.lig_time_ms <- stats.lig_time_ms +. vpie_stats.vpi_time_ms
          ; stats.lig_ce <- stats.lig_ce + vpie_stats.vpi_ce
          ; stats._VPIE <- vpie_stats :: stats._VPIE
          ; ZProc.close_scope z3
          ; ((ZProc.implication_counter_example z3 sygus.pre_func.body inv), inv)
      end
  ) with Some ce, _
         -> restart_with_new_states (random_value ~seed:(`Deterministic seed_string)
                                                  (gen_state_from_model sygus (Some ce)))
       | None, inv
         -> Log.info (lazy ("Starting with the following initial invariant:"
                           ^ (Log.indented_sep 4) ^ inv))
          ; match satisfyTrans ~config ~sygus ~states ~neg_states ~z3 inv stats with
            | inv, None
              -> if not (String.equal inv "false") then ((ZProc.simplify z3 inv), stats)
                  else restart_with_new_states (random_value ~seed:(`Deterministic seed_string)
                                                             (gen_pre_state ~use_trans:true sygus z3))
            | _, (Some ce_model)
              -> restart_with_new_states (random_value ~seed:(`Deterministic seed_string)
                                                       (gen_state_from_model sygus (Some ce_model)))

let learnInvariant ?(config = Config.default) ~(states : Value.t list list) ~(neg_states : Value.t list list)
                   ~(zpath : string) (sygus : SyGuS.t) : Job.desc * stats =
  let open ZProc in
  let stats = { _VPIE = [] ; lig_time_ms = 0.0 ; lig_ce = 0 }
  in process ~zpath
       ~random_seed:(Some (Int.to_string (Quickcheck.(random_value ~seed:(`Deterministic config.base_random_seed)
                                                                   (Generator.small_non_negative_int)))))
       (fun z3 -> StateSampler.setup sygus z3 ~user_features:(List.map ~f:fst config.user_features)
                ; if not (Option.is_none (implication_counter_example z3 sygus.pre_func.body sygus.post_func.body))
                  then ("false", stats)
                  else learnInvariant_internal ~config ~states ~neg_states sygus config.base_random_seed z3 stats)