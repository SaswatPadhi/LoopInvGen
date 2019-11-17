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

  constants : Value.t list ;
  functions : func list ;
  variables : var list ;
  synth_variables : var list ;
}

let replace bindings expr =
  if bindings = [] then expr else
  let table = ref (String.Map.empty)
   in List.iter bindings
                ~f:(function [@warning "-8"]
                    | List [ (Atom key) ; data ]      (* SMTLIB *)
                    | List [ (Atom key) ; _ ; data ]  (* SyGuS *)
                    -> table := String.Map.add_exn !table ~key ~data)
    ; let rec helper = function
        | List l -> List (List.map l ~f:helper)
        | Atom atom -> match String.Map.find !table atom with
                       | None      -> Atom atom
                       | Some data -> data
       in helper expr

let rec remove_lets : Sexp.t -> Sexp.t = function
  | Atom _ as atom -> atom
  | List [ (Atom "let") ; List bindings ; body ]
    -> replace bindings (remove_lets body)
  | List l -> List (List.map l ~f:remove_lets)

let rec extract_consts : Sexp.t -> Value.t list = function
  | List [] -> []
  | (Atom a) | List [Atom a] -> (try [ Value.of_string a ] with _ -> [])
  | List(_ :: fargs)
    -> let consts = List.fold fargs ~init:[] ~f:(fun consts farg -> (extract_consts farg) @ consts)
        in List.(dedup_and_sort ~compare:Value.compare consts)

let parse_variable_declaration : Sexp.t -> var = function
  | List [ Atom v ; Atom t ] -> (v, (Type.of_string t))
  | List [ Atom v ; List [Atom "_"; Atom "BitVec"; Atom n]] -> (v, (Type.of_params ("BitVec", (int_of_string n))))
  | sexp -> raise (Parse_Exn ("Invalid variable usage: " ^ (Sexp.to_string_hum sexp)))

let parse_define_fun : Sexp.t list -> func * Value.t list = function
  | [Atom(name) ; List(args) ; Atom(r_typ) ; expr]
    -> let args = List.map ~f:parse_variable_declaration args in
       let expr = remove_lets expr in
       let consts = extract_consts expr
        in ({ name = name
            ; body = (Sexp.to_string_hum expr)
            ; args = args
            ; return = (Type.of_string r_typ)
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
  "(declare-var " ^ var_name ^ " " ^ (Type.to_string var_type) ^ ")"

let parse_sexps (sexps : Sexp.t list) : t =
  let logic : string ref = ref "" in
  let consts : Value.t list ref = ref [] in
  let funcs : func list ref = ref [] in
  let invf_name : string ref = ref "" in
  let postf_name : string ref = ref "" in
  let pref_name : string ref = ref "" in
  let transf_name : string ref = ref "" in
  let variables : var list ref = ref [] in
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
                -> let new_var = parse_variable_declaration (List sexps)
                    in if List.mem !variables new_var ~equal:(fun x y -> String.equal (fst x) (fst y))
                       then raise (Parse_Exn ("Multiple declarations of variable " ^ (fst new_var)))
                       else variables := new_var :: !variables
              | List [ (Atom "declare-fun") ; name ; args ; rtype ]
                -> if args <> List [] then raise (Parse_Exn "Only nullary function (i.e. variable) declarations supported.") else
                   let new_var = parse_variable_declaration (List [name ; rtype])
                    in if List.mem !variables new_var ~equal:(fun x y -> String.equal (fst x) (fst y))
                       then raise (Parse_Exn ("Multiple declarations of variable " ^ (fst new_var)))
                       else variables := new_var :: !variables
              | List ( (Atom "declare-primed-var") :: sexps )
                -> let _var, _type = parse_variable_declaration (List sexps)
                    in if List.mem !variables (_var, _type) ~equal:(fun x y -> String.equal (fst x) (fst y))
                       then raise (Parse_Exn ("Multiple declarations of variable " ^ _var))
                       else variables := (_var, _type) :: (_var ^ "!", _type) :: !variables
              | List ( (Atom "define-fun") :: func_sexps )
                -> let (func, fconsts) = parse_define_fun func_sexps
                    in if List.mem !funcs func ~equal:(fun x y -> String.equal x.name y.name)
                       (* FIXME: SyGuS format allows overloaded functions with different signatures *)
                       then raise (Parse_Exn ("Multiple definitions of function " ^ func.name))
                       else funcs := func :: !funcs ; consts := fconsts @ !consts
              | List [ (Atom "inv-constraint") ; (Atom _invf_name) ; (Atom _pref_name)
                                               ; (Atom _transf_name) ; (Atom _postf_name) ]
                -> pref_name := _pref_name ; transf_name := _transf_name ; postf_name := _postf_name
                 ; if not (String.equal !invf_name _invf_name)
                   then raise (Parse_Exn ("Invariant function [" ^ _invf_name ^ "] not declared"))
              | sexp -> raise (Parse_Exn ("Unknown command: " ^ (Sexp.to_string_hum sexp))))
    ; consts := List.dedup_and_sort ~compare:Poly.compare !consts
    ; Log.debug (lazy ("Detected Constants: " ^ (List.to_string_map ~sep:", " ~f:Value.to_string !consts)))
    ; if String.equal !logic ""
      then (logic := "LIA" ; Log.debug (lazy ("Using default logic: LIA")))
    ; { constants = !consts
      ; functions = List.rev !funcs
      ; logic = !logic
      ; post_func = List.find_exn ~f:(fun f -> String.equal f.name !postf_name) !funcs
      ; pre_func = List.find_exn ~f:(fun f -> String.equal f.name !pref_name) !funcs
      ; trans_func = List.find_exn ~f:(fun f -> String.equal f.name !transf_name) !funcs
      ; variables = !variables
      ; synth_variables = !invf_vars
      ; inv_func =
        { args = !invf_vars
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
