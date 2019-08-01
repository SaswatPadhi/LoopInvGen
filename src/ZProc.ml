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

let rec print_list = function 
[] -> ()
| e::l -> print_string e ; print_string " " ; print_list l

  
let write_to_z3_query_file str is_append =
  let filename = "smt_queries.smt2" in (
  let outc =Out_channel.create ~append:is_append filename in
  protect ~f:(fun ()->fprintf outc "%s\n" str)
  ~finally:(fun() ->Out_channel.close outc))
  
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
     ;write_to_z3_query_file (String.concat ~sep:"\n" init_options) false
     ;Out_channel.output_lines z3.stdin init_options
     ; (match random_seed with
        | None -> ()
        | Some seed -> Out_channel.output_lines z3.stdin [
                         "(set-option :auto_config false)" ;
                         "(set-option :smt.phase_selection 5)" ;
                         "(set-option :smt.arith.random_initial_value true)" ;
                         "(set-option :smt.random_seed " ^ seed ^ ")"
                       ];

                       write_to_z3_query_file (String.concat ~sep:"\n" [
                        "(set-option :auto_config false)" ;
                        "(set-option :smt.phase_selection 5)" ;
                        "(set-option :smt.arith.random_initial_value true)" ;
                        "(set-option :smt.random_seed " ^ seed ^ ")"
                      ]) true
          )
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
        in if l = last_line then ()
           else if l <> "" then (lines := l :: (!lines) ; read_line ())
       in read_line () ; lines := List.rev (!lines)
        ; Log.debug (lazy ("    " ^ (String.concat (!lines) ~sep:(Log.indented_sep 4))))
        ; String.concat ~sep:" " (!lines)

let create_scope ?(db = []) (z3 : t) : unit =
  Log.debug (lazy (String.concat ("Created z3 scope." :: db)
                                 ~sep:(Log.indented_sep 4))) ;
  write_to_z3_query_file (String.concat ~sep:"\n" ("(push)" :: db)) true;
  Out_channel.output_lines z3.stdin ("(push)" :: db)

let close_scope (z3 : t) : unit =
  Log.debug (lazy ("Closed z3 scope.")) ;
  write_to_z3_query_file ("(pop)\n") true;
  Out_channel.output_string z3.stdin "(pop)\n"

let run_queries ?(scoped = true) (z3 : t) ?(db = []) (queries : string list)
                : string list =      
  if queries = []
  then begin
    if not scoped && db <> [] then
      begin
        Log.debug (lazy (String.concat ("New z3 call:" :: db) ~sep:(Log.indented_sep 4)))
        ;write_to_z3_query_file (String.concat ~sep:"\n" db) true
      ; Out_channel.output_lines z3.stdin db
      end ; []
    end
  else begin
    let results = ref []
     in (if scoped then create_scope z3 else ())
      ; Log.debug (lazy (String.concat ("New z3 call:" :: (db @ queries))
                           ~sep:(Log.indented_sep 4)))
      ; write_to_z3_query_file (String.concat ~sep:"\n" db) true
      ; Out_channel.output_lines z3.stdin db
      ; Log.debug (lazy "Results:")
      ; List.iter queries ~f:(fun q ->
          write_to_z3_query_file q true;
          write_to_z3_query_file "\n" true;
          Out_channel.output_string z3.stdin q ;
          Out_channel.newline z3.stdin ;
          results := (flush_and_collect z3) :: (!results))
      ; (if scoped then close_scope z3 else ())
      ; List.rev (!results)
  end

let lamda_sexpt_to_list (sexp: Sexp.t): (t * t) list * t = 
  let open Sexp in 
  match sexp with 
  | _ -> raise (Internal_Exn ("Unable to deserialize lamda: "
                              ^ (to_string_hum sexp)))
                              

let z3_sexp_to_value (sexp : Sexp.t) : Value.t =  
  let open Sexp in    
  match sexp with   
  | _ -> Value.of_string sexp
  (* print_string (Value.to_string (Value.of_string sexp)); *)
        (* (Int 1) *)  
        
let contains_string s1 s2 =
  try
    let len = String.length s2 in
    for i = 0 to String.length s1 - len do
      if String.sub s1 i len = s2 then raise Exit
    done;
    false
  with Exit -> true

(* let z3_result_to_model (result : string list) : model option =
  let intermediate_result = z3_result_to_model_helper result
   in  *)

let z3_result_to_model (result : string list) : model option =
  let open Sexp in
  try [@warning "-8"]
  match result with
  | "unsat" :: _ -> None
  | [ "sat" ; _ ; result ]
    -> begin match Sexp.parse result with
        | Done (List((Atom _) :: varexps), _)
          -> let open List in
            Some (filter_map varexps ~f:(
              function
              | List(l) -> let (Atom n, v) = (nth_exn l 1) , (nth_exn l 4)
                            in match v with
                               | List [ _ ; Atom "as-array" ; func_name]
                                 -> let Some val_sexp = List.find_map varexps ~f:(function List l -> let name, value = (nth_exn l 1), (nth_exn l 4)
                                                                                                      in if Sexp.equal func_name name then Some value else None)
                                     in Some (n, (Value.parse_array [] val_sexp))
                               | _ -> try Some (n, (z3_sexp_to_value v))
                                      with _ -> None))
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
  let open Sexp in
  let goal =
    match
      run_queries z3 ~db:["(assert " ^ q ^ ")"]
                  ["(apply (repeat (then simplify ctx-simplify ctx-solver-simplify)))"]
    with [ goal ] -> goal
       | goals -> raise (Internal_Exn ("Unexpected z3 goals:\n" ^ (String.concat ~sep:"\n" goals)))
  in match Sexp.parse goal with
     | Done (List [ (Atom "goals") ; (List ((Atom "goal") :: goalexpr)) ], _)
       -> let goals = List.(filter_map (drop (rev goalexpr) 4)
                                       ~f:(function Atom "true" -> None
                                                  | Atom atom -> Some atom
                                                  | l -> Some (to_string_hum l)))
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
