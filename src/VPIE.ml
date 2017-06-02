open Core
open PIE

let rec learnVPreCond ?(strengthen = false) ?(k = 1) ?(auto_incr_k = true)
                      ?(consts = []) ?(disable_synth = false) ?(max_tries = 512)
                      ?(cnf_opt_to_desc = PIE.cnf_opt_to_desc) ~(z3 : ZProc.t)
                      ((job, post_desc) : ('a, 'b) job with_desc) : desc =
  if max_tries < 1 then cnf_opt_to_desc None
  else begin
    let precond = learnPreCond ~strengthen ~k ~auto_incr_k ~consts
                               ~disable_synth job
    in let pre_desc = cnf_opt_to_desc precond
    in Log.debug (lazy ("Candidate Precondition: " ^ pre_desc))
     ; match ZProc.implication_counter_example z3 pre_desc post_desc with
       | None -> ZProc.simplify z3 pre_desc
       | Some model
         -> let model = Hashtbl.Poly.of_alist_exn model in
            let test = List.map job.farg_names ~f:(Hashtbl.find_exn model)
            in Log.debug (lazy ("Counter example: "
                               ^ (Types.serialize_values ~sep:", " test)))
             ; learnVPreCond ~strengthen ~k ~auto_incr_k ~consts ~disable_synth
                             ~max_tries:(max_tries - 1) ~cnf_opt_to_desc ~z3
                             ((add_tests ~job [test]), post_desc)
  end