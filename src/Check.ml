open Core

open Utils

type result = PASS | FAIL of (string list) | NO_SOLUTION_PASS | NO_SOLUTION_FAIL

let is_sufficient_invariant ~(zpath : string) ~(sygus : SyGuS.t) (inv : string) : result =
  let open ZProc
   in process ~zpath (fun z3 ->
     StateSampler.setup sygus z3 ;
     if not ( Option.is_none (implication_counter_example z3 sygus.pre_func.body sygus.post_func.body))
     then (if String.equal inv "false" then NO_SOLUTION_PASS else NO_SOLUTION_FAIL)
     else let inv = SyGuS.func_definition {sygus.inv_func with body = inv}
           in ignore (run_queries ~scoped:false z3 [] ~db:[ inv ]) ;
              let inv_call = "(" ^ sygus.inv_func.name ^ " "
                           ^ (List.to_string_map sygus.inv_func.args ~sep:" " ~f:fst)
                           ^ ")"
               in match [ (implication_counter_example z3 sygus.pre_func.body inv_call)
                        ; (implication_counter_example z3
                             ("(and " ^ sygus.trans_func.body ^ " " ^ inv_call ^ ")")
                             ("(" ^ sygus.inv_func.name ^ " "
                             ^ (List.to_string_map sygus.inv_func.args ~sep:" "
                                  ~f:(fun (s, _) -> s ^ "!"))
                             ^ ")"))
                        ; (implication_counter_example z3 inv_call sygus.post_func.body) ]
                  with
                  | [ None ; None ; None ] -> PASS
                  | x -> FAIL (List.filter_mapi x
                                 ~f:(fun i v -> if Option.is_none v then None
                                                else Some [| "pre" ; "trans" ; "post" |].(i))))