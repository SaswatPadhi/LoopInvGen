open Core_kernel

open PIE
open Types
open Utils

type 'a config = {
  for_PIE : PIE.config ;

  base_random_seed : string ;
  describe : (('a feature with_desc) CNF.t option) -> desc ;
  max_tries : int ;
  simplify : bool ;
}

let default_config = {
  for_PIE = PIE.default_config ;

  base_random_seed = "VPIE" ;
  describe = PIE.cnf_opt_to_desc ;
  max_tries = 512 ;
  simplify = true ;
}

let learnVPreCond ?(conf = default_config) ?(eval_term = "true") ~(z3 : ZProc.t)
                  ?(consts = []) (job_post : ('a, 'b) job with_desc) : desc =
  let rec helper tries_left (job, post_desc) =
    if conf.max_tries > 0 && tries_left < 1
    then (Log.error (lazy ("VPIE Reached MAX attempts ("
                          ^ (Int.to_string conf.max_tries)
                          ^ "). Giving up ..."))
         ; conf.describe None)
    else begin
      Log.info (lazy ("VPIE Attempt "
                      ^ (Int.to_string (1 + conf.max_tries - tries_left))
                      ^ "/" ^ (Int.to_string conf.max_tries) ^ ".")) ;
      match learnPreCond ~conf:conf.for_PIE ~consts job with
      | None | Some [[]] -> conf.describe None
      | precond
        -> let pre_desc = conf.describe precond
            in Log.debug (lazy ("Candidate Precondition: " ^ pre_desc))
              ; begin match ZProc.implication_counter_example ~eval_term z3
                                                        pre_desc post_desc with
                | None -> let pre_desc =
                            if conf.simplify then ZProc.simplify z3 pre_desc
                                              else pre_desc
                          in Log.debug (lazy ("Verified Precondition: " ^ pre_desc))
                            ; pre_desc
                | Some model
                  -> let model = Hashtbl.Poly.of_alist_exn model in
                      let test =
                        List.map2_exn job.farg_names job.farg_types
                          ~f:(fun n t -> match Hashtbl.find model n with
                                        | Some v -> v
                                        | None
                                          -> let open Quickcheck
                                              in random_value (GenTests.typ_gen t)
                                                  ~size:1
                                                  ~seed:(`Deterministic (
                                                    conf.base_random_seed ^
                                                    (string_of_int tries_left))))
                      in Log.debug (lazy ("Counter example: {"
                                        ^ (List.to_string_map2
                                             test job.farg_names ~sep:", "
                                             ~f:(fun v n -> n ^ " = " ^
                                                            (serialize_value v)))
                                        ^ "}"))
                      ; helper (tries_left - 1) ((add_neg_test ~job test), post_desc)
                end
    end
  in helper conf.max_tries job_post