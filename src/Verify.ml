open Core
open Core.Out_channel
open Exceptions
open SyGuS
open Utils

type result = PASS | FAIL of (string list) | IMPOSSIBLE_PASS | IMPOSSIBLE_FAIL

let checkInvariant ~(zpath : string) ~(sygus : SyGuS.t) (inv : string) : result =
  let open ZProc in process ~zpath (fun z3 ->
    Simulator.setup sygus z3 ;
    if not ((implication_counter_example z3 sygus.pre.expr sygus.post.expr) = None)
    then (if inv = "" then IMPOSSIBLE_PASS else IMPOSSIBLE_FAIL)
    else let inv = (if inv <> "" then inv else build_inv_func "false" ~sygus) in (
      ignore (run_queries ~local:false z3 [] ~db:[ inv ]) ;
      let inv_call = "(" ^ sygus.inv_name ^ " "
                   ^ (List.to_string_map sygus.inv_vars ~sep:" " ~f:fst)
                   ^ ")" in
        match [ (implication_counter_example z3 sygus.pre.expr inv_call)
              ; (implication_counter_example z3
                    ("(and " ^ sygus.trans.expr ^ " " ^ inv_call ^ ")")
                    ("(" ^ sygus.inv_name ^ " "
                    ^ (List.to_string_map sygus.inv_vars ~sep:" "
                        ~f:(fun (s, _) -> s ^ "!"))
                    ^ ")"))
              ; (implication_counter_example z3 inv_call sygus.post.expr) ]
        with [ None ; None ; None ] -> PASS
        | x -> FAIL (List.filter_mapi x
                       ~f:(fun i v -> if v = None then None
                                      else Some [| "pre" ; "trans"
                                                 ; "post" |].(i)))))

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
  | FAIL x -> "FAIL [" ^ (String.concat x ~sep:" , ") ^ "]"
  | IMPOSSIBLE_PASS -> "PASS (NO SOLUTION)"
  | IMPOSSIBLE_FAIL -> "FAIL (NO SOLUTION)"

let exit_code_of_result res =
  match res with
  | PASS -> 0
  | FAIL _ -> 1
  | IMPOSSIBLE_PASS -> 2
  | IMPOSSIBLE_FAIL -> 3

let main zpath invfile logfile filename () =
  Utils.start_logging_to ~msg:"CHECK" logfile ;
  let sygus = SyGuS.load ~shrink:false (Utils.get_in_channel filename) in
  let inv = read_inv_from_chan (Utils.get_in_channel invfile) ~sygus in
  let res = checkInvariant ~zpath ~sygus inv
  in output_lines stdout [string_of_result res]
   ; exit (exit_code_of_result res)

let cmd =
  Command.basic_spec
    ~summary: "Check sufficiency of a generated invariant for proving correctness."
    Command.Spec.(
      empty
      +> flag "-z" (required string)  ~doc:"FILENAME path to the z3 executable"
      +> flag "-i" (required string)  ~doc:"FILENAME input file containing the loop invariant"
      +> flag "-l" (optional string)  ~doc:"FILENAME output file for logs, defaults to null"
      +> anon (maybe_with_default "-" ("filename" %: file))
    )
    main

let () =
  Command.run
    ~version:"0.6b"
    ~build_info:("padhi @ " ^ (Core_extended.Logger.timestamp ()))
    cmd