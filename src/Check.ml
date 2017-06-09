open Core
open Core.Out_channel
open Exceptions
open SyGuS
open Utils

type result = PASS | FAIL | IMPOSSIBLE_PASS | IMPOSSIBLE_FAIL

let checkInvariant (inv : string) ~(sygus : SyGuS.t) : result =
  let open ZProc in process (fun z3 ->
    Simulator.setup sygus z3 ;
    if not ((implication_counter_example z3 sygus.pre.expr sygus.post.expr)
            = None)
    then (if inv = "" then IMPOSSIBLE_PASS else IMPOSSIBLE_FAIL)
    else if inv = "" then FAIL else (
      ignore (run_queries ~local:false z3 [] ~db:[ inv ]) ;
      let inv_call = "(" ^ sygus.inv_name ^ " "
                   ^ (List.to_string_map sygus.inv_vars ~sep:" " ~f:fst)
                   ^ ")" in
        match [ (implication_counter_example z3 sygus.pre.expr inv_call)
              ; (implication_counter_example z3
                    ("(and " ^ sygus.trans.expr ^ " " ^ inv_call ^ ")")
                    ("(" ^ sygus.inv_name ^ " "
                    ^ (List.to_string_map sygus.inv'_vars ~sep:" " ~f:fst)
                    ^ ")"))
              ; (implication_counter_example z3 inv_call sygus.post.expr) ]
        with [ None ; None ; None ] -> PASS | _ -> FAIL))

let read_inv_from_chan in_chan ~(sygus : SyGuS.t) : string =
  let open Sexplib.Sexp in
  let sexps = input_rev_sexps in_chan
  in match sexps with
     | [] -> ""
     | [ (List [ (Atom "define-fun") ; (Atom name) ; _ ; (Atom "Bool") ; body ])
         as inv ] when name = sygus.inv_name
       -> begin match body with
           | (Atom "false") -> ""
           | _ -> to_string_hum inv
          end
     | _ -> raise (Parse_Exn "Multiple Sexps detected, expecting a single invariant.")

let string_of_result res =
  match res with
  | PASS -> "PASS"
  | FAIL -> "FAIL"
  | IMPOSSIBLE_PASS -> "PASS (NO SOLUTION)"
  | IMPOSSIBLE_FAIL -> "FAIL (NO SOLUTION)"

let exit_code_of_result res =
  match res with
  | PASS -> 0
  | FAIL -> 1
  | IMPOSSIBLE_PASS -> 2
  | IMPOSSIBLE_FAIL -> 3

let main invfile do_log filename () =
  (if do_log then Log.enable ~msg:"VERIFIER" () else ()) ;
  let sygus = SyGuS.load (Utils.get_in_channel filename) in
  let inv = read_inv_from_chan (Utils.get_in_channel invfile) ~sygus in
  let res = checkInvariant inv ~sygus
  in output_lines stdout [string_of_result res]
   ; exit (exit_code_of_result res)

let cmd =
  Command.basic
    ~summary: "Check sufficiency of a generated invariant for proving correctness."
    Command.Spec.(
      empty
      +> flag "-i" (required string)  ~doc:"FILENAME invariant file"
      +> flag "-l" (no_arg)           ~doc:"enable logging"
      +> anon (maybe_with_default "-" ("filename" %: file))
    )
    main

let () =
  Command.run
    ~version:"0.6b"
    ~build_info:("padhi @ " ^ (Core_extended.Logger.timestamp ()))
    cmd