open Core
open LoopInvGen
open LoopInvGen.Utils

type result = PASS | FAIL of (string list) | NO_SOLUTION_PASS | NO_SOLUTION_FAIL

let check_invariant ~(zpath : string) ~(sygus : SyGuS.t) (inv : string) : result =
  let open ZProc in process ~zpath (fun z3 ->
    Simulator.setup sygus z3 ;
    if not ((implication_counter_example z3 sygus.pre_func.expr sygus.post_func.expr) = None)
    then (if String.equal inv "false" then NO_SOLUTION_PASS else NO_SOLUTION_FAIL)
    else let inv = SyGuS.func_definition {sygus.inv_func with expr = inv}
          in (ignore (run_queries ~scoped:false z3 [] ~db:[ inv ]) ;
              let inv_call = "(" ^ sygus.inv_func.name ^ " "
                           ^ (List.to_string_map sygus.inv_func.args ~sep:" " ~f:fst)
                           ^ ")"
               in match [ (implication_counter_example z3 sygus.pre_func.expr inv_call)
                        ; (implication_counter_example z3
                             ("(and " ^ sygus.trans_func.expr ^ " " ^ inv_call ^ ")")
                             ("(" ^ sygus.inv_func.name ^ " "
                             ^ (List.to_string_map sygus.inv_func.args ~sep:" "
                                  ~f:(fun (s, _) -> s ^ "!"))
                             ^ ")"))
                        ; (implication_counter_example z3 inv_call sygus.post_func.expr) ]
                  with [ None ; None ; None ] -> PASS
                  | x -> FAIL (List.filter_mapi x
                                 ~f:(fun i v -> if v = None then None
                                                else Some [| "pre" ; "trans" ; "post" |].(i)))))

let read_inv_from_chan in_chan ~(sygus : SyGuS.t) : Sexplib.Sexp.t =
  let open Sexplib.Sexp in
  let sexps = input_rev_sexps in_chan
  in match sexps with
     | [] | [ (List [Atom "fail"]) ] -> Atom "false"
     | [ List [ (Atom "define-fun") ; (Atom name) ; (List vars) ; (Atom "Bool") ; body ] ]
       when String.equal name sygus.inv_func.name
       -> let helper expr old_v new_v =
           let rec internal_helper = function
             | Atom s -> Atom (if String.equal s old_v then new_v else s)
             | List s -> List (List.map ~f:internal_helper s)
            in internal_helper expr
       in List.foldi vars ~init:body
            ~f:(fun [@warning "-8"] i cur_body (List [ (Atom v) ; _ ])
                -> helper cur_body v (fst (List.nth_exn sygus.inv_func.args i)))
     | _ -> raise (Exceptions.Parse_Exn
                     "Multiple Sexps detected, expecting a single invariant.")

let string_of_result res =
  match res with
  | PASS -> "PASS"
  | FAIL x -> "FAIL {" ^ (String.concat x ~sep:";") ^ "}"
  | NO_SOLUTION_PASS -> "PASS (NO SOLUTION)"
  | NO_SOLUTION_FAIL -> "FAIL (NO SOLUTION)"

let exit_code_of_result res =
  match res with
  | PASS -> 0
  | FAIL _ -> 1
  | NO_SOLUTION_PASS -> 2
  | NO_SOLUTION_FAIL -> 3

let main zpath filename logfile invfile () =
  Log.enable ~msg:"VERIFY" logfile ;
  let sygus = SyGuS.parse (get_in_channel filename) in
  let inv = read_inv_from_chan (get_in_channel invfile) ~sygus in
  let res =
    try check_invariant ~zpath ~sygus (Sexplib.Sexp.to_string_hum inv)
    with _ -> FAIL [ "<parse>" ]
   in Stdio.Out_channel.output_string Stdio.stdout (string_of_result res)
    ; Caml.exit (exit_code_of_result res)

let spec =
  let open Command.Spec in (
    empty
    +> flag "-z" (required string)
       ~doc:"FILENAME path to the z3 executable"
    +> flag "-s" (required string)
       ~doc:"FILENAME input file containing the SyGuS-INV problem"
    +> flag "-l" (optional string)
       ~doc:"FILENAME output file for logs, defaults to null"
    +> anon (maybe_with_default "-" ("filename" %: file))
  )

let () =
  Command.run
    (Command.basic_spec spec main
       ~summary: "Check sufficiency of a generated invariant for proving correctness.")
