open Core

open Exceptions
open Sexplib
open Utils

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
[@@inline always]

let flush_and_collect (z3 : t) : string =
  let last_line = "THIS.LINE>WILL.BE#PRINTED=AFTER+THE-RESULT."
  in Out_channel.output_string z3.stdin ("\n(echo \"" ^ last_line ^ "\")\n")
   ; Out_channel.flush z3.stdin
   ; let lines = ref [] in
     let rec read_line () : unit =
       let l = Option.value (In_channel.input_line z3.stdout) ~default:""
        in if String.equal l last_line then ()
           else if not (String.equal l "") then (lines := l :: (!lines) ; read_line ())
       in read_line () ; lines := List.rev (!lines)
        ; Log.debug (lazy ("    " ^ (String.concat (!lines) ~sep:(Log.indented_sep 4))))
        ; String.concat ~sep:" " (!lines)

let create_scope ?(db = []) (z3 : t) : unit =
  Log.debug (lazy (String.concat ("Created z3 scope." :: db)
                                 ~sep:(Log.indented_sep 4))) ;
  Out_channel.output_lines z3.stdin ("(push)" :: db)

let close_scope (z3 : t) : unit =
  Log.debug (lazy ("Closed z3 scope.")) ;
  Out_channel.output_string z3.stdin "(pop)\n"

let run_queries ?(scoped = true) (z3 : t) ?(db = []) (queries : string list)
                : string list =
  if List.is_empty queries
  then begin
    if not scoped && not (List.is_empty db) then
      begin
        Log.debug (lazy (String.concat ("New z3 call:" :: db) ~sep:(Log.indented_sep 4)))
      ; Out_channel.output_lines z3.stdin db
      end ; []
    end
  else begin
    let results = ref []
     in (if scoped then create_scope z3 else ())
      ; Log.debug (lazy (String.concat ("New z3 call:" :: (db @ queries))
                           ~sep:(Log.indented_sep 4)))
      ; Out_channel.output_lines z3.stdin db
      ; Log.debug (lazy "Results:")
      ; List.iter queries ~f:(fun q ->
          Out_channel.output_string z3.stdin q ;
          Out_channel.newline z3.stdin ;
          results := (flush_and_collect z3) :: (!results))
      ; (if scoped then close_scope z3 else ())
      ; List.rev (!results)
  end

let z3_sexp_to_value (sexp : Sexp.t) : Value.t =
  let open Sexp in
  match sexp with
  | _ -> Value.of_sexp sexp

let reduced_exps (varexps : Sexp.t list) =
  let symbol_table = String.Table.create () in
  let reduced_varexps = (
    List.filter_map varexps ~f:(fun [@warning "-8"] (List l)
                                -> let (Atom n, v) = (List.nth_exn l 1) , (List.nth_exn l 4)
                                    in match v with
                                       | List [ _ ; Atom "as-array" ; Atom func_name ]
                                         -> (Hashtbl.set symbol_table func_name n) ; None
                                       | _ -> Some l))
  in (reduced_varexps , symbol_table)

let z3_result_to_model (result : string list) : model option =
  let open Sexp in
  try [@warning "-8"]
  match result with
  | "unsat" :: _ -> None
  | [ "sat" ; _ ; result ]
    -> begin match Sexp.parse result with
         | Done (List((Atom _) :: varexps), _)
           -> let varexprs, symtab = (reduced_exps varexps)
               in Some (List.map varexprs ~f:(fun l
                  -> let (Atom n, v) = (List.nth_exn l 1) , (List.nth_exn l 4) in
                     let binding = Hashtbl.find symtab n
                      in match binding with
                         | Some name -> begin
                             let key_type_repr, val_type, value = List.((nth_exn l 2), (nth_exn l 3), (nth_exn l 4))
                              in (name, (Value.parse_named_array value key_type_repr val_type))
                           end
                         | None -> (n, (z3_sexp_to_value v))))
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
    ~db:(("(assert (not (and (=> " ^ a ^ " " ^ b ^ ") (=> " ^ b ^ " " ^ a ^ "))))") :: db)

let simplify (z3 : t) (q : string) : string =
  let goal =
    match
      run_queries z3 ~db:["(assert " ^ q ^ ")"]
                  ["(apply (repeat (then purify-arith simplify ctx-simplify ctx-solver-simplify)))"]
    with [ goal ] -> goal
       | goals -> raise (Internal_Exn ("Unexpected z3 goals:\n" ^ (String.concat ~sep:"\n" goals)))
  in match Sexp.parse goal with
     | Done (List [ (Atom "goals") ; (List ((Atom "goal") :: goalexpr)) ], _)
       -> let goals = List.(filter_map (drop (rev goalexpr) 4)
                                       ~f:(function Atom "true" -> None
                                                  | Atom atom -> Some atom
                                                  | l -> Some (Sexp.to_string_hum l)))
           in if List.is_empty goals then "true"
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

let model_to_constraint ?(negate=false) ?(ignore_primed=false) (model : model) : string =
   (if negate then "(not (and " else "(and ")
 ^ (List.filter_map model ~f:(fun (n, v) -> if ignore_primed && String.is_suffix n ~suffix:"!"
                                            then None
                                            else Some ("(= " ^ n ^ " " ^ (Value.to_string v) ^ ")"))
      |> String.concat ~sep:" ")
 ^ (if negate then "))" else ")")

let collect_models ?(eval_term = "true") ?(db = []) ?(n = 1) ?(init = None) ?(run = fun _ -> ()) (z3 : t)
                   : model list =
  let query = query_for_model ~eval_term ()
   in create_scope z3
    ; ignore (run_queries ~scoped:false z3 ~db [])
    ; let rec helper accum = function
        | 0 -> accum
        | r -> match
                 match accum with
                   | [] -> z3_result_to_model (run_queries z3 query ~scoped:false)
                   | h :: _ -> z3_result_to_model (run_queries ~scoped:false z3 query
                                 ~db:[ "(assert " ^ (model_to_constraint ~negate:true ~ignore_primed:true h) ^ ")" ])
               with
               | None -> accum
               | Some model -> run model
                             ; helper (model :: accum) (r - 1)
       in let result = helper (match init with None -> [] | Some m -> [m]) n
           in close_scope z3
            ; result

let build_feature (name : string) (z3 : t) (vals : Value.t list) : bool =
  let arguments = List.to_string_map vals ~sep:" " ~f:Value.to_string in
  let result = run_queries z3 ~db:["(assert (" ^ name ^ " " ^ arguments ^ "))"]
                           ["(check-sat)"]
   in match result with
      | ["sat"] -> true
      | ["unsat"] -> false
      | _ -> raise (Internal_Exn ("Failed to build feature" ^ name ^ "."))