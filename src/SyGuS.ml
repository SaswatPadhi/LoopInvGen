(* TODO: Refactor in to ocaml-sygus package. *)

open Core

open Exceptions
open Sexplib.Type
open Utils

type var = string * Type.t

type func = {
  args : var list ;
  name : string ;
  body : string ;
  return : Type.t ;
  expressible : bool ;
}

type t = {
  logic : string ;

  inv_func : func ;
  post_func : func ;
  pre_func : func ;
  trans_func : func ;
  trans_branches : string list ;

  constants : Value.t list ;
  functions : func list ;
  variables : var list ;
  synth_variables : var list ;
}

let rec extract_consts : Sexp.t -> Value.t list = function
  | List [] -> []
  | (Atom a) | List [Atom a] -> (try [ Value.of_atomic_string a ] with _ -> [])
  | List(_ :: fargs)
    -> let consts = List.fold fargs ~init:[] ~f:(fun consts farg -> (extract_consts farg) @ consts)
        in List.(dedup_and_sort ~compare:Value.compare consts)

let parse_variable_declaration : Sexp.t -> var = function
  | List [ Atom v ; t ] -> (v, (Type.of_sexp t))
  | sexp -> raise (Parse_Exn ("Invalid variable usage: " ^ (Sexp.to_string_hum sexp)))

let parse_define_fun : Sexp.t list -> func * Value.t list = function
  | [Atom(name) ; List(args) ; r_typ ; expr]
    -> let args = List.map ~f:parse_variable_declaration args in
       let expr = remove_lets expr in
       let consts = extract_consts expr
        in ({ name = name
            ; body = (Sexp.to_string_hum expr)
            ; args = args
            ; return = (Type.of_sexp r_typ)
            ; expressible = true (* TODO: Check if function is expressible in the provided grammar, when we sypport it. *)
            }, consts)
  | sexp_list -> raise (Parse_Exn ("Invalid function definition: "
                                  ^ (Sexp.to_string_hum (List(Atom("define-fun") :: sexp_list)))))

let func_definition (f : func) : string =
  "(define-fun " ^ f.name ^ " ("
  ^ (List.to_string_map
       f.args ~sep:" " ~f:(fun (v, t) -> "(" ^ v ^ " " ^ (Type.to_string t) ^ ")"))
  ^ ") " ^ (Type.to_string f.return) ^ " " ^ f.body ^ ")"

let var_declaration ((var_name, var_type) : var) : string =
  "(declare-const " ^ var_name ^ " " ^ (Type.to_string var_type) ^ ")"

let parse_sexps (sexps : Sexp.t list) : t =
  let logic : string ref = ref "" in
  let consts : Value.t list ref = ref [] in
  let funcs : func list ref = ref [] in
  let invf_name : string ref = ref "" in
  let postf_name : string ref = ref "" in
  let pref_name : string ref = ref "" in
  let transf_name : string ref = ref "" in
  let variables : var list ref = ref [] in
  let extra_variables : var list ref = ref [] in
  let invf_vars : var list ref = ref []
   in List.iter sexps
        ~f:(function
              | List [ (Atom "check-synth") ] -> ()
              | List [ (Atom "set-logic") ; (Atom _logic) ]
                -> if String.equal !logic "" then logic := _logic
                   else raise (Parse_Exn ("Logic already set to: " ^ !logic))
              | List [ (Atom "synth-inv") ; (Atom _invf_name) ; (List _invf_vars) ]
                -> invf_name := _invf_name ; invf_vars := List.map ~f:parse_variable_declaration _invf_vars
              | List [ (Atom "synth-inv") ; (Atom _invf_name) ; (List _invf_vars) ; _ ]
                -> (* FIXME: Custom grammar *) Log.error (lazy ("LoopInvGen currently does not allow custom grammars."))
                 ; invf_name := _invf_name ; invf_vars := List.map ~f:parse_variable_declaration _invf_vars
              | List ( (Atom "declare-var") :: sexps )
                -> extra_variables := (parse_variable_declaration (List sexps)) :: !extra_variables
              | List ( (Atom "define-fun") :: func_sexps )
                -> let (func, fconsts) = parse_define_fun func_sexps
                    in if List.mem !funcs func ~equal:(fun x y -> String.equal x.name y.name)
                       (* FIXME: SyGuS format allows overloaded functions with different signatures *)
                       then raise (Parse_Exn ("Multiple definitions of function " ^ func.name))
                       else funcs := func :: !funcs ; consts := fconsts @ !consts
              | List [ (Atom "inv-constraint") ; (Atom _invf_name) ; (Atom _pref_name)
                                               ; (Atom _transf_name) ; (Atom _postf_name) ]
                -> pref_name := _pref_name ; transf_name := _transf_name ; postf_name := _postf_name
                 ; (if not (String.equal !invf_name _invf_name)
                    then raise (Parse_Exn ("Invariant function [" ^ _invf_name ^ "] not declared")))
                 ; variables := (!invf_vars @ (List.map !invf_vars ~f:(fun (v,t) -> (v^"!",t)))) ;
                 let [@warning "-8"] [pref; transf; postf]  = List.map [_pref_name ; _transf_name ; _postf_name]
                                                ~f:(fun name -> List.find !funcs ~f:(fun func -> String.equal func.name name)) in
                 (match pref with Some pref -> if not (List.equal (fun (v1, _) (v2, _) -> String.equal v1 v2) pref.args !invf_vars)
                                               then raise (Parse_Exn ("[" ^ _invf_name ^ "] and [" ^ _pref_name ^ "] have inconsistent arguments!"))
                                | _ -> raise (Parse_Exn ("Precondition [" ^ _pref_name ^ "] not defined!")))
                 ; (match postf with Some postf -> if not (List.equal (fun (v1, _) (v2, _) -> String.equal v1 v2) postf.args !invf_vars)
                                                   then raise (Parse_Exn ("[" ^ _invf_name ^ "] and [" ^ _postf_name ^ "] have inconsistent arguments!"))
                                   | _ -> raise (Parse_Exn ("Postcondition [" ^ _postf_name ^ "] not defined!")))
                 ; (match transf with Some transf -> if not (List.equal (fun (v1, _) (v2, _) -> String.equal v1 v2) transf.args !variables)
                                                     then raise (Parse_Exn ("[" ^ _invf_name ^ "] and [" ^ _transf_name ^ "] have inconsistent arguments!"))
                                    | _ -> raise (Parse_Exn ("Transition function [" ^ _transf_name ^ "] not defined!")))
              | sexp -> raise (Parse_Exn ("Unknown command: " ^ (Sexp.to_string_hum sexp))))
    ; consts := List.dedup_and_sort ~compare:Poly.compare !consts
    ; Log.debug (lazy ("Detected Constants: " ^ (List.to_string_map ~sep:", " ~f:Value.to_string !consts)))
    ; if String.equal !logic ""
      then (logic := "LIA" ; Log.debug (lazy ("Using default logic: LIA")))
    ; let dups = List.filter !extra_variables ~f:(List.mem !variables ~equal:(fun x y -> String.equal (fst x) (fst y)))
       in if not (List.is_empty dups)
          then raise (Parse_Exn ( "Multiple declarations of ["
                                ^ (List.to_string_map dups ~sep:", " ~f:fst)
                                ^ "]"))
          else { constants = !consts
               ; functions = List.rev !funcs
               ; logic = !logic
               ; post_func = List.find_exn ~f:(fun f -> String.equal f.name !postf_name) !funcs
               ; pre_func = List.find_exn ~f:(fun f -> String.equal f.name !pref_name) !funcs
               ; trans_func = List.find_exn ~f:(fun f -> String.equal f.name !transf_name) !funcs
               ; trans_branches = []
               ; variables = !extra_variables @ !variables
               ; synth_variables = !invf_vars
               ; inv_func = { args = !invf_vars
                            ; name = !invf_name
                            ; body = ""
                            ; return = Type.BOOL
                            ; expressible = true
                            }
               }

let parse (chan : Stdio.In_channel.t) : t =
  parse_sexps (Sexplib.Sexp.input_sexps chan)

let write_to (filename : string) (sygus : t) : unit =
  let out_chan = Stdio.Out_channel.create filename
   in Caml.Marshal.to_channel out_chan sygus []
    ; Stdio.Out_channel.close out_chan

let read_from (filename : string) : t =
  let in_chan = Stdio.In_channel.create filename in
  let sygus = Caml.Marshal.from_channel in_chan
   in Stdio.In_channel.close in_chan
    ; sygus

let translate_smtlib_expr (expr : string) : string =
  if (String.equal expr "true") || (String.equal expr "false") then expr else
  let open Sexp in
  let rec helper = function
    | List [ (Atom "-") ; (Atom num) ] when (String.for_all num ~f:Char.is_digit)
      -> Atom ("-" ^ num)
    | List [ (Atom "-") ; name ]
      -> List [ (Atom "-") ; (Atom "0") ; name ]
    | List [ (Atom "let") ; List bindings ; body ]
      -> replace (List.map bindings
                           ~f:(function [@warning "-8"]
                               | List [ key ; data ]
                                 -> List [ key ; (helper data) ]))
                 (helper body)
    | List l -> List (List.map l ~f:helper)
    | sexp -> sexp
  in match Sexplib.Sexp.parse expr with
     | Done (sexp, _) -> Sexp.to_string_hum (helper (sexp))
     | _ -> expr (* TODO: parse does not work on single atoms *)
