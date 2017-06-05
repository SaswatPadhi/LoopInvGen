open Core
open Core.Unix
open Exceptions
open Sexplib
open Utils

type t = {
  pid    : Pid.t ;
  stdin  : Out_channel.t ;
  stdout : In_channel.t ;
  stderr : In_channel.t ;
}

type model = (string * Types.value) list

let query_for_model ?(eval_term = "true") () =
  [ "(check-sat)"
  (* forces Z3 to generate complete models over variables in `eval_term` *)
  ; "(eval " ^ eval_term ^ " :completion true)"
  ; "(get-model)" ]

let create () : t =
  let open Process_info in
  let pi = create_process "./_dep/z3.bin" ["-in"] in
    Log.info (lazy ("Created z3 instance. PID = " ^ (Pid.to_string pi.pid))) ;
    {
      pid    = pi.pid ;
      stdin  = out_channel_of_descr pi.stdin ;
      stdout = in_channel_of_descr pi.stdout ;
      stderr = in_channel_of_descr pi.stdout ;
    }

let close z3 =
  Out_channel.close z3.stdin ; ignore (waitpid z3.pid) ;
  Log.info (lazy ("Closed z3 instance. PID = " ^ (Pid.to_string z3.pid)))

let process (f : t -> 'a) : 'a =
  let z3 = create () in let result = (f z3) in (close z3) ; result

let flush_and_collect (z3 : t) : string =
  let last_line = "ABRACADABRA.ABRACADABRA^ABRACADABRA"
  in Out_channel.output_string z3.stdin ("\n(echo \"" ^ last_line ^ "\")\n")
   ; Out_channel.flush z3.stdin
   ; let lines = ref [] in
     let rec read_line () : unit =
       let l = Option.value (In_channel.input_line z3.stdout) ~default:""
        in if l = last_line then ()
           else if l <> "" then (lines := l :: (!lines) ; read_line ())
       in read_line () ; lines := List.rev (!lines)
        ; Log.debug (lazy (String.concat ("Result:" :: (!lines))
                                         ~sep:Log.indented_sep))
        ; String.concat ~sep:" " (!lines)

let create_local ?(db = []) (z3 : t) : unit =
  Log.debug (lazy (String.concat ("Created Z3 local." :: db)
                                 ~sep:Log.indented_sep)) ;
  Out_channel.output_lines z3.stdin ("(push)" :: db) ;
  Out_channel.flush z3.stdin

let close_local (z3 : t) : unit =
  Log.debug (lazy ("Closed Z3 local.")) ;
  Out_channel.output_lines z3.stdin ["(pop)"] ;
  Out_channel.flush z3.stdin

let run_queries ?(local = true) (z3 : t) ?(db = []) (queries : string list)
                : string list =
  (if local then create_local z3 else ()) ;
  Log.debug (lazy (String.concat ("New Z3 call:" :: (db @ queries))
                                 ~sep:Log.indented_sep)) ;
  if queries = []
  then begin
    if local then () else
      Out_channel.output_lines z3.stdin db ;
      Out_channel.flush z3.stdin ; []
    end
  else let results = ref []
       in Out_channel.output_lines z3.stdin db
        ; List.iter queries ~f:(fun q ->
            Out_channel.output_string z3.stdin q ;
            Out_channel.newline z3.stdin ;
            results := (flush_and_collect z3) :: (!results)
          )
        ; (if local then close_local z3 else ())
        ; Out_channel.flush z3.stdin ; List.rev (!results)

let z3_sexp_to_value (sexp : Sexp.t) : Types.value =
  let open Sexp in
  let unexpected_exn = Internal_Exn ("Unexpected z3 value: "
                                    ^ (to_string_hum sexp)) in
  let vstr = match sexp with
             | Atom v -> v
             | List([(Atom "-") ; (Atom v)]) -> "-" ^ v
             | _ -> raise unexpected_exn
  in Option.value_exn (Types.deserialize_value vstr)

let z3_result_to_values (result : string list) : model option =
  let open Sexp in
  let unexpected_exn = Internal_Exn ("Unexpected z3 model: " ^ (String.concat ~sep:"\n" result)) in
    match result with
    | "unsat" :: _ -> None
    | [ "sat" ; _ ; result ]
      -> begin match Sexp.parse result with
          | Done (List((Atom model) :: varexps), _)
            -> let open List in
              Some (map varexps ~f:(
                function
                | List(l) -> begin match (nth_exn l 1) , (nth_exn l 4) with
                              | (Atom n, v) -> (n, (z3_sexp_to_value v))
                              | _ -> raise unexpected_exn
                              end
                | _ -> raise unexpected_exn))
          | _ -> raise unexpected_exn
        end
    | _ -> raise unexpected_exn

let implication_counter_example ?(eval_term = "true") ?(db = []) (z3 : t)
                                (a : string) (b : string) : model option =
  z3_result_to_values (
    run_queries z3 ~db:(db @ [ "(assert (not (=> " ^ a ^ " " ^ b ^")))" ])
                (query_for_model ~eval_term ()))

let equivalence_counter_example ?(eval_term = "true") ?(db = []) (z3 : t)
                                (a : string) (b : string) : model option =
  z3_result_to_values (
    run_queries z3 ~db:(db @ [ "(assert (not (=> " ^ a ^ " " ^ b ^")))"
                             ; "(assert (not (=> " ^ b ^ " " ^ a ^")))" ])
                (query_for_model ~eval_term ()))

let simplify (z3 : t) (q : string) : string =
  let open Sexp in
  let goal =
    match
      run_queries z3 ~db:["(assert " ^ q ^ ")"]
                  ["(apply (then simplify ctx-simplify ctx-solver-simplify))"]
    with [ goal ] -> goal
        | goals -> raise (Internal_Exn ("Unexpected goals:\n"
                                       ^ (String.concat ~sep:"\n" goals)))
  in let unexpected_exn = Internal_Exn ("Unexpected z3 goals: " ^ goal)
  in match Sexp.parse goal with
     | Done (List([(Atom "goals") ; (List((Atom "goal") :: goalexpr))]), _)
       -> let goals = List.filter_map goalexpr
                        ~f:(function Atom("true") -> Some "true"
                                   | Atom("false") -> Some "false"
                                   | Atom(_) -> None
                                   | l -> Some (to_string_hum l))
          in let goalstr = String.concat ~sep:" " goals
          in if List.length goals < 2 then goalstr else "(and " ^ goalstr ^ ")"
     | _ -> raise unexpected_exn

let model_to_string ?(rowsep = "\n") ?(colsep = ": ") (model : model option)
                    : string =
  match model with
  | None   -> ""
  | Some m -> List.to_string_map m ~sep:rowsep
                ~f:(fun (n, v) -> n ^ colsep ^ (Types.serialize_value v))