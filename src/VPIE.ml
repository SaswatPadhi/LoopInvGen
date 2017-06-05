open Core
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

let rec learnVPreCond ?(conf = default_config) ?(eval_term = "true")
                      ?(consts = []) ~(z3 : ZProc.t)
                      ((job, post_desc) : ('a, 'b) job with_desc) : desc =
  if conf.max_tries < 1 then conf.describe None
  else begin
    let precond = learnPreCond ~conf:conf.for_PIE ~consts job
    in let pre_desc = conf.describe precond
    in Log.debug (lazy ("Candidate Precondition: " ^ pre_desc))
     ; match ZProc.implication_counter_example ~eval_term z3
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
                                    in random_value (GenTests.typ_gen t) ~size:1
                                         ~seed:(`Deterministic (
                                           conf.base_random_seed ^
                                           (string_of_int conf.max_tries))))
            in Log.debug (lazy ("Counter example: {"
                               ^ (List.to_string_map2
                                    test job.farg_names ~sep:", "
                                    ~f:(fun v n -> n ^ " = " ^
                                                   (serialize_value v)))
                               ^ "}"))
             ; let (job, tests_added) = add_tests ~job [test]
                in if tests_added < 1 then "false"
                   else learnVPreCond (job, post_desc) ~eval_term ~z3 ~consts
                          ~conf: { conf with max_tries = (conf.max_tries - 1) }
  end