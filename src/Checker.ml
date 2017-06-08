open Core
open Core.Out_channel
open Exceptions
open SyGuS
open Utils

let checkInvariant (inv : string) ~(sygus : SyGuS.t) : bool =
  let open ZProc in process (fun z3 ->
    Simulator.setup sygus z3 ;
    if not ((implication_counter_example z3 sygus.pre.expr sygus.post.expr)
            = None)
    then inv = "" else if inv = "" then false else begin
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
        with [ None ; None ; None ] -> true | _ -> false
    end)

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

let main invfile do_log filename () =
  (if do_log then Log.enable ~msg:"VERIFIER" () else ()) ;
  let sygus = SyGuS.load (Utils.get_in_channel filename) in
  let inv = read_inv_from_chan (Utils.get_in_channel invfile) ~sygus in
  let result = checkInvariant inv ~sygus
   in exit (if result then 0 else 1)

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