open Core_kernel

open Utils

module Config = struct
  let base_additional_counterexamples = 2

  type 'a t = {
    _PIE : PIE.Config.t ;

    num_counterexamples: int ;
    base_random_seed : string ;
    describe : (('a Job.feature Job.with_desc) CNF.t option) -> Job.desc ;
    max_attempts : int ;
    do_simplify : bool ;
  }

  let default : 'a t = {
    _PIE = PIE.Config.default ;

    num_counterexamples = base_additional_counterexamples ;
    base_random_seed = "VPIE" ;
    describe = PIE.cnf_opt_to_desc ;
    max_attempts = 2 ;
    do_simplify = true ;
  }
end

type stats = {
  mutable vpi_ce : int ;
  mutable vpi_time_ms : float ;
  mutable _PIE : PIE.stats list ;
} [@@deriving sexp]

let learnVPreCond ?(config = Config.default) ?(eval_term = "true") ~(z3 : ZProc.t)
                  ?(consts = []) ~(post_desc : Job.desc) (job : Job.t)
                  : Job.desc * stats =
  let stats = { _PIE = [] ; vpi_time_ms = 0.0 ; vpi_ce = 0 } in
  let rec helper tries_left job =
    if config.max_attempts > 0 && tries_left < 1
    then (Log.error (lazy ("VPIE Reached MAX attempts ("
                            ^ (Int.to_string config.max_attempts)
                            ^ "). Giving up ..."))
         ; (config.describe None, stats)) 
    else begin      
      Log.info (lazy ("VPIE Attempt "
                      ^ (Int.to_string (1 + config.max_attempts - tries_left))
                      ^ "/" ^ (Int.to_string config.max_attempts) ^ ".")) ;
      match PIE.learnPreCond ~config:config._PIE ~consts job with
      | (None, pie_stats) | ((Some [[]]), pie_stats)
        -> Log.error (lazy ("Failed to learn a verified precondition!"))
         ; stats._PIE <- pie_stats :: stats._PIE
         ; stats.vpi_time_ms <- stats.vpi_time_ms +. pie_stats.pi_time_ms
         ; ((config.describe None), stats)
      | (precond, pie_stats)
        -> stats._PIE <- pie_stats :: stats._PIE
         ; stats.vpi_time_ms <- stats.vpi_time_ms +. pie_stats.pi_time_ms
         ; let pre_desc = config.describe precond
            in Log.info (lazy ("Candidate Precondition: " ^ pre_desc))
             ; begin match ZProc.implication_counter_example
                             ~eval_term z3 pre_desc post_desc with
               | None -> let pre_desc = if config.do_simplify
                                        then ZProc.simplify z3 pre_desc
                                        else pre_desc
                          in Log.info (lazy ("Verified Precondition: " ^ pre_desc))
                           ; (pre_desc, stats)
               | Some model
                 -> let models = ZProc.collect_models
                                   z3 ~init:(Some model) ~eval_term
                                   ~n:(config.num_counterexamples - 1)
                                   ~db:[ "(assert (not (=> " ^ pre_desc ^ " " ^ post_desc ^ ")))" ]
                     in let tests = List.map models ~f:(fun model ->
                          let model = Hashtbl.Poly.of_alist_exn model in
                          let test =
                            List.map2_exn job.farg_names job.farg_types
                              ~f:(fun n t -> match Hashtbl.find model n with
                                             | Some v -> v
                                             | None -> let open Quickcheck
                                                        in random_value (TestGen.for_type t)
                                                             ~size:1
                                                             ~seed:(`Deterministic (
                                                               config.base_random_seed ^
                                                               (string_of_int tries_left))))
                           in Log.info (lazy ("Counterexample: {"
                                             ^ (List.to_string_map2
                                                  test job.farg_names ~sep:", "
                                                  ~f:(fun v n -> n ^ " = " ^ (Value.to_string v)))
                                             ^ "}"))
                            ; test)
                         in stats.vpi_ce <- stats.vpi_ce + 1
                          ; helper (tries_left - 1)
                                   (List.fold tests ~init:job ~f:(fun job test -> Job.add_neg_test ~job test))
               end
    end
  in try helper config.max_attempts job
     with e -> Log.error (lazy (Exn.to_string e))
             ; ("false" , stats)
