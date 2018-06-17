open Core

open Exceptions
open Utils

type result = PASS | FAIL of (string list) | IMPOSSIBLE_PASS | IMPOSSIBLE_FAIL

let check_invariant ~(zpath : string) ~(sygus : SyGuS.t) (inv : string) : result =
  let open ZProc in process ~zpath (fun z3 ->
    Simulator.setup sygus z3 ;
    if not ((implication_counter_example z3 sygus.pre_func.expr sygus.post_func.expr) = None)
    then (if String.equal inv "" then IMPOSSIBLE_PASS else IMPOSSIBLE_FAIL)
    else let inv = (if not (String.equal inv "") then inv
                    else SyGuS.func_definition {sygus.inv_func with expr = "false"})
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

let read_inv_from_chan in_chan ~(sygus : SyGuS.t) : string =
  let open Sexplib.Sexp in
  let sexps = input_rev_sexps in_chan
  in match sexps with
     | [] -> ""
     | [ (List [ (Atom "define-fun") ; (Atom name) ; _ ; (Atom "Bool") ; body ]) as inv ]
       when String.equal name sygus.inv_func.name
       -> begin match body with
           | (Atom "false") -> ""
           | _ -> to_string_hum inv
          end
     | _ -> raise (Parse_Exn "Multiple Sexps detected, expecting a single invariant.")

let string_of_result res =
  match res with
  | PASS -> "PASS"
  | FAIL x -> "FAIL {" ^ (String.concat x ~sep:";") ^ "}"
  | IMPOSSIBLE_PASS -> "PASS (NO SOLUTION)"
  | IMPOSSIBLE_FAIL -> "FAIL (NO SOLUTION)"

let exit_code_of_result res =
  match res with
  | PASS -> 0
  | FAIL _ -> 1
  | IMPOSSIBLE_PASS -> 2
  | IMPOSSIBLE_FAIL -> 3

let main zpath invfile logfile filename () =
  Log.enable ~msg:"VERIFY" logfile ;
  let sygus = SyGuS.parse (get_in_channel filename) in
  let res = check_invariant ~zpath ~sygus (read_inv_from_chan (get_in_channel invfile) ~sygus)
  in Stdio.Out_channel.output_string Stdio.stdout (string_of_result res)
   ; Caml.exit (exit_code_of_result res)

let spec =
  let open Command.Spec in (
    empty
    +> flag "-z" (required string)  ~doc:"FILENAME path to the z3 executable"
    +> flag "-i" (required string)  ~doc:"FILENAME input file containing the loop invariant"
    +> flag "-l" (optional string)  ~doc:"FILENAME output file for logs, defaults to null"
    +> anon (maybe_with_default "-" ("filename" %: file))
  )

let () =
  Command.run
    (Command.basic_spec spec main
       ~summary: "Check sufficiency of a generated invariant for proving correctness.")