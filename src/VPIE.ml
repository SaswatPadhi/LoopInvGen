open Core
open PIE
open Types
open Utils

let rec learnVPreCond ?(strengthen = false) ?(describe = PIE.cnf_opt_to_desc)
                      ?(k = 1) ?(auto_incr_k = true) ?(disable_synth = false)
                      ?(max_c_group_size = 20) ?(max_tries = 512) ?(consts = [])
                      ?(simplify = true) ?(base_random_seed = "PIE")
                      ?(eval_term = "true") ~(z3 : ZProc.t)
                      ((job, post_desc) : ('a, 'b) job with_desc) : desc =
  if max_tries < 1 then cnf_opt_to_desc None
  else begin
    let precond = learnPreCond ~strengthen ~k ~auto_incr_k ~consts
                               ~max_c_group_size ~disable_synth job
    in let pre_desc = describe precond
    in Log.debug (lazy ("Candidate Precondition: " ^ pre_desc))
     ; match ZProc.implication_counter_example ~eval_term z3
                                               pre_desc post_desc with
       | None -> let pre_desc =
                   if simplify then ZProc.simplify z3 pre_desc else pre_desc
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
                                           base_random_seed ^
                                           (string_of_int max_tries))))
            in Log.debug (lazy ("Counter example: {"
                               ^ (List.to_string_map2
                                    test job.farg_names ~sep:", "
                                    ~f:(fun v n -> n ^ " = " ^
                                                   (serialize_value v)))
                               ^ "}"))
             ; learnVPreCond ~strengthen ~describe ~k ~auto_incr_k ~consts ~z3
                             ~disable_synth ~max_c_group_size ~base_random_seed
                             ~max_tries:(max_tries - 1) ~simplify ~eval_term
                             ((add_tests ~job [test]), post_desc)
  end