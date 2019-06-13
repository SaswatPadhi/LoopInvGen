open Core

open LoopInvGen
open LoopInvGen.Check
open LoopInvGen.Utils

let read_inv_from_chan in_chan ~(sygus : SyGuS.t) : Sexplib.Sexp.t =
  let open Sexplib.Sexp in
  let sexps = input_rev_sexps in_chan
  in match sexps with
     | [] | [ (List [Atom "fail"]) ] -> Atom "false"
     | [ List [ (Atom "define-fun") ; (Atom name) ; (List vars) ; (Atom "Bool") ; body ] ]
       when String.equal name sygus.inv_func.name
       -> let replace_var expr old_v new_v =
           let rec helper = function
             | Atom s -> Atom (if String.equal s old_v then new_v else s)
             | List s -> List (List.map ~f:helper s)
            in helper expr
          in List.foldi vars ~init:body
                        ~f:(fun [@warning "-8"] i cur_body (List [ (Atom v) ; _ ])
                            -> replace_var cur_body v
                                           (fst (List.nth_exn sygus.inv_func.args i)))
     | _ -> raise (Exceptions.Parse_Exn
                     "Bad/multiple S-exprs detected, expecting invariant as a single valid S-expr.")

let string_of_result = function
  | PASS -> "PASS"
  | FAIL x -> "FAIL {" ^ (String.concat x ~sep:";") ^ "}"
  | NO_SOLUTION_PASS -> "PASS (NO SOLUTION)"
  | NO_SOLUTION_FAIL -> "FAIL (NO SOLUTION)"

let exit_code_of_result = function
  | PASS -> 0
  | FAIL _ -> 10
  | NO_SOLUTION_PASS -> 0
  | NO_SOLUTION_FAIL -> 11

let main zpath filename logfile invfile () =
  Log.enable ~msg:"VERIFY" logfile ;
  let sygus = SyGuS.parse (get_in_channel filename) in
  let inv = read_inv_from_chan (get_in_channel invfile) ~sygus in
  let res =
    try is_sufficient_invariant ~zpath ~sygus (Sexplib.Sexp.to_string_hum inv)
    with _ -> FAIL [ "<parse>" ]
   in Out_channel.output_string Stdio.stdout (string_of_result res)
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
