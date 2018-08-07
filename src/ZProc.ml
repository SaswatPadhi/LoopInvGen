open Core

open Exceptions
open Sexplib

type t = {
  procid : Pid.t ;
  stdin  : Out_channel.t ;
  stdout : In_channel.t ;
  stderr : In_channel.t ;
}

type model = (string * Value.t) list

let query_for_model ?(eval_term = "true") () =
  [ "(check-sat)"
    (* forces z3 to generate complete models over variables in `eval_term` *)
  ; "(eval " ^ eval_term ^ " :completion true)"
  ; "(get-model)" ]

let create ?(init_options = []) ?(random_seed = None) (zpath : string) : t =
  let open Unix in
  let open Process_info in
  let pi = create_process ~prog:zpath ~args:["-in";"-smt2"] in
  let z3 = {
    procid = pi.pid ;
    stdin  = out_channel_of_descr pi.stdin ;
    stdout = in_channel_of_descr pi.stdout ;
    stderr = in_channel_of_descr pi.stdout ;
  } in Log.debug (lazy ("Created z3 instance. PID = " ^ (Pid.to_string pi.pid)))
     ; Out_channel.output_lines z3.stdin init_options
     ; (match random_seed with
        | None -> ()
        | Some seed -> Out_channel.output_lines z3.stdin [
                         "(set-option :auto_config false)" ;
                         "(set-option :smt.phase_selection 5)" ;
                         "(set-option :smt.arith.random_initial_value true)" ;
                         "(set-option :smt.random_seed " ^ seed ^ ")"
                       ])
     ; z3

let close z3 =
  Out_channel.close z3.stdin ; ignore (Unix.waitpid z3.procid) ;
  Log.debug (lazy ("Closed z3 instance. PID = " ^ (Pid.to_string z3.procid)))

let process ?(init_options = []) ?(random_seed = None)
            ~(zpath : string) (f : t -> 'a) : 'a =
  let z3 = create ~init_options ~random_seed zpath in
  let result = (f z3) in (close z3) ; result

let flush_and_collect (z3 : t) : string =
  let last_line = "THIS.LINE>WILL.BE#PRINTED=AFTER+THE-RESULT."
  in Out_channel.output_string z3.stdin ("\n(echo \"" ^ last_line ^ "\")\n")
   ; Out_channel.flush z3.stdin
   ; let lines = ref [] in
     let rec read_line () : unit =
       let l = Option.value (In_channel.input_line z3.stdout) ~default:""
        in if l = last_line then ()
           else if l <> "" then (lines := l :: (!lines) ; read_line ())
       in read_line () ; lines := List.rev (!lines)
        ; Log.debug (lazy ("    " ^ (String.concat (!lines) ~sep:(Log.indented_sep 4))))
        ; String.concat ~sep:" " (!lines)

let create_scope ?(db = []) (z3 : t) : unit =
  Log.debug (lazy (String.concat ("Created z3 scope." :: db)
                                 ~sep:(Log.indented_sep 4))) ;
  Out_channel.output_lines z3.stdin ("(push)" :: db) ;
  Out_channel.flush z3.stdin

let close_scope (z3 : t) : unit =
  Log.debug (lazy ("Closed z3 scope.")) ;
  Out_channel.output_string z3.stdin "(pop)\n" ;
  Out_channel.flush z3.stdin

let run_queries ?(scoped = true) (z3 : t) ?(db = []) (queries : string list)
                : string list =
  (if scoped then create_scope z3 else ()) ;
  Log.debug (lazy (String.concat ("New z3 call:" :: (db @ queries))
                                 ~sep:(Log.indented_sep 4))) ;
  if queries = []
  then begin
    if scoped then () else
      Out_channel.output_lines z3.stdin db ;
      Out_channel.flush z3.stdin ; []
    end
  else let results = ref []
       in Out_channel.output_lines z3.stdin db
        ; Log.debug (lazy "Results:")
        ; List.iter queries ~f:(fun q ->
            Out_channel.output_string z3.stdin q ;
            Out_channel.newline z3.stdin ;
            results := (flush_and_collect z3) :: (!results)
          )
        ; (if scoped then close_scope z3 else ())
        ; Out_channel.flush z3.stdin ; List.rev (!results)

let z3_sexp_to_value (sexp : Sexp.t) : Value.t =
  let open Sexp in
  let vstr = match sexp with
             | Atom v -> v
             | List([(Atom "-") ; (Atom v)]) -> "-" ^ v
             | _ -> raise (Internal_Exn ("Unable to deserialize value: "
                                        ^ (to_string_hum sexp)))
  in Value.of_string vstr

let z3_result_to_model (result : string list) : model option =
  let open Sexp in
  try [@warning "-8"]
  match result with
  | "unsat" :: _ -> None
  | [ "sat" ; _ ; result ]
    -> begin match Sexp.parse result with
        | Done (List((Atom _) :: varexps), _)
          -> let open List in
            Some (map varexps ~f:(
              function
              | List(l) -> let (Atom n, v) = (nth_exn l 1) , (nth_exn l 4)
                            in (n, (z3_sexp_to_value v))))
      end
  with e -> Log.error (lazy ("Error parsing z3 model: "
                            ^ (String.concat ~sep:"\n" result)
                            ^ "\n\n" ^ (Exn.to_string e)))
          ; raise e

let sat_model_for_asserts ?(eval_term = "true") ?(db = []) (z3 : t)
                          : model option =
  z3_result_to_model (run_queries z3 (query_for_model ~eval_term ()) ~db)

let implication_counter_example ?(eval_term = "true") ?(db = []) (z3 : t)
                                (a : string) (b : string) : model option =
  sat_model_for_asserts z3 ~eval_term
                        ~db:(("(assert (not (=> " ^ a ^ " " ^ b ^")))") :: db)

let equivalence_counter_example ?(eval_term = "true") ?(db = []) (z3 : t)
                                (a : string) (b : string) : model option =
  sat_model_for_asserts z3 ~eval_term
                        ~db:(("(assert (not (=> " ^ a ^ " " ^ b ^")))") ::
                             ("(assert (not (=> " ^ b ^ " " ^ a ^")))") :: db)

let simplify (z3 : t) (q : string) : string =
  let open Sexp in
  let goal =
    match
      run_queries z3 ~db:["(assert " ^ q ^ ")"]
                  ["(apply (then simplify ctx-simplify ctx-solver-simplify))"]
    with [ goal ] -> goal
       | goals -> raise (Internal_Exn ("Unexpected z3 goals:\n"
                                      ^ (String.concat ~sep:"\n" goals)))
  in match Sexp.parse goal with
     | Done (List([(Atom "goals") ; (List((Atom "goal") :: goalexpr))]), _)
       -> let goals = List.filter_map goalexpr
                        ~f:(function Atom("true") -> Some "true"
                                   | Atom("false") -> Some "false"
                                   | Atom(_) -> None
                                   | l -> Some (to_string_hum l))
          in if List.length goals = 0 then "true"
             else (let goalstr = String.concat ~sep:" " goals
                   in if List.length goals < 2 then goalstr else "(and " ^ goalstr ^ ")")
     | _ -> raise (Internal_Exn ("Unexpected z3 goals: " ^ goal))

let constraint_sat_function (expr : string) ~(z3 : t) ~(arg_names : string list)
                            : (Value.t list -> Value.t) =
  fun (values : Value.t list) ->
    match run_queries z3
            ~db:(("(assert " ^ expr ^ ")") ::
                (List.map2_exn arg_names values
                               ~f:(fun n v -> ("(assert (= " ^ n ^ " " ^
                                               (Value.to_string v) ^ "))"))))
            [ "(check-sat)" ]
    with [ "sat" ]   -> Value.Bool true
       | [ "unsat" ] -> Value.Bool false
       | _ -> raise (Internal_Exn "z3 could not verify the query.")