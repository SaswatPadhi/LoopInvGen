(* TODO: Refactor in to ocaml-sygus package. *)

open Base

open Exceptions
open Sexplib.Type
open Utils

type var = string * Type.t

type func = {
  args : var list ;
  name : string ;
  expr : string ;
  return : Type.t ;
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

let rec extract_consts (exp : Sexp.t) : (Value.t list) =
  match exp with
  | List([]) -> []
  | (Atom a) | List([Atom a]) -> (try [ Value.of_string a ] with _ -> [])
  (* FIXME: Handling let expressins needs  more work:
     let in SyGuS format looks like (let ((<symb> <sort> <term>)+) <term>),
     but in Z3 the syntax is (let ((<symb> <term>)+) <term>).

  | List [(Atom "let") ; (List let_bindings) ; let_expr]
    -> let (bind_vars, args_in_bind , consts_in_bind) =
         List.fold let_bindings ~init:([],[],[])
                   ~f:(fun[@warning "-8"] (symbs, args, consts) (List [(Atom l_symb) ; (Atom l_typ) ; l_term]) ->
                         let (a, c) = extract_used_args_and_consts vars l_term
                         in (((l_symb, (to_typ l_typ)) :: symbs), (a @ args), (c @ consts)))
       in let (args , consts) = extract_used_args_and_consts (bind_vars @ vars) let_expr
       in let args = List.(filter args ~f:(fun a -> not (mem ~equal:Poly.equal bind_vars a)))
       in List.((dedup_and_sort ~compare:Poly.compare (args @ args_in_bind)),
                (dedup_and_sort ~compare:Poly.compare (consts @ consts_in_bind))) *)
  | List ((Atom "let") :: _)
    -> raise (Parse_Exn ("`let` constructs are currently not supported: " ^ (Sexp.to_string_hum exp)))
  | List(_ :: fargs)
    -> let consts = List.fold fargs ~init:[] ~f:(fun consts farg -> (extract_consts farg) @ consts)
        in List.(dedup_and_sort ~compare:Value.compare consts)

let parse_variable_declaration (sexp : Sexp.t) : var =
  match sexp with
  | List([Atom(v) ; Atom(t)]) -> (v, (Type.of_string t))
  | _ -> raise (Parse_Exn ("Invalid variable usage: " ^ (Sexp.to_string_hum sexp)))

let parse_define_fun (sexp_list : Sexp.t list) : func * Value.t list =
  match sexp_list with
  | [Atom(name) ; List(args) ; Atom(r_typ) ; expr]
    -> let args = List.map ~f:parse_variable_declaration args in
       let consts = extract_consts expr
       in ({ name = name
           ; expr = (Sexp.to_string_hum expr)
           ; args = args
           ; return = (Type.of_string r_typ)
           }, consts)
  | _ -> raise (Parse_Exn ("Invalid function definition: "
                          ^ (Sexp.to_string_hum (List(Atom("define-fun") :: sexp_list)))))

let func_definition (f : func) : string =
  "(define-fun " ^ f.name ^ " ("
  ^ (List.to_string_map
       f.args ~sep:" " ~f:(fun (v, t) -> "(" ^ v ^ " " ^ (Type.to_string t) ^ ")"))
  ^ ") " ^ (Type.to_string f.return) ^ " " ^ f.expr ^ ")"

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
              | List([Atom("check-synth")]) -> ()
              | List([Atom("set-logic"); Atom(_logic)])
                -> if String.equal !logic "" then logic := _logic
                   else raise (Parse_Exn ("Logic already set to: " ^ !logic))
              | List([Atom("synth-inv") ; Atom(_invf_name) ; List(_invf_vars)])
                -> invf_name := _invf_name ; invf_vars := List.map ~f:parse_variable_declaration _invf_vars
              | List([Atom("synth-inv") ; Atom(_invf_name) ; List(_invf_vars) ; _])
                -> (* TODO *) Log.warn (lazy ("LoopInvGen currently does not allow custom grammars. The provided grammar will be ignored, and full SMTLIB2 will be used instead."))
                 ; invf_name := _invf_name ; invf_vars := List.map ~f:parse_variable_declaration _invf_vars
              | List(Atom("declare-var") :: sexps)
                -> let new_var = parse_variable_declaration (List sexps)
                    in if List.mem !variables new_var ~equal:(fun x y -> String.equal (fst x) (fst y))
                       then raise (Parse_Exn ("Multiple declarations of variable " ^ (fst new_var)))
                       else variables := new_var :: !variables
              | List(Atom("declare-primed-var") :: sexps)
                -> let _var, _type = parse_variable_declaration (List sexps)
                    in if List.mem !variables (_var, _type) ~equal:(fun x y -> String.equal (fst x) (fst y))
                       then raise (Parse_Exn ("Multiple declarations of variable " ^ _var))
                       else variables := (_var, _type) :: (_var ^ "!", _type) :: !variables
              | List(Atom("define-fun") :: func_sexps)
                -> let (func, fconsts) = parse_define_fun func_sexps
                    in if List.mem !funcs func ~equal:(fun x y -> String.equal x.name y.name)
                       (* FIXME: SyGuS format allows overloaded functions with different signatures *)
                       then raise (Parse_Exn ("Multiple definitions of function " ^ func.name))
                       else funcs := func :: !funcs ; consts := fconsts @ !consts
              | List([Atom("inv-constraint") ; Atom(_invf_name) ; Atom(_pref_name)
                                             ; Atom(_transf_name) ; Atom(_postf_name) ])
                -> pref_name := _pref_name ; transf_name := _transf_name ; postf_name := _postf_name
                 ; if not (String.equal !invf_name _invf_name)
                   then raise (Parse_Exn ("Invariant function [" ^ _invf_name ^ "] not declared"))
              | _ as sexp -> raise (Parse_Exn ("Unknown command: " ^ (Sexp.to_string_hum sexp))))
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
        ; expr = ""
        ; return = Type.BOOL
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
  let rec replace name expr body =
    match body with
    | Atom a when String.equal a name -> expr
    | List(l) -> List(List.map l ~f:(replace name expr))
    | _ -> body
  in let rec helper sexp =
    match sexp with
    | List([Atom("-") ; Atom(num)]) when (String.for_all num ~f:Char.is_digit)
      -> Atom("-" ^ num)
    | List([Atom("-") ; name])
      -> List([Atom("-") ; Atom("0") ; name])
    | List([Atom("let") ; List([List([Atom(name) ; expr])]) ; body])
      -> helper (replace name expr body)
    | List(l) -> List(List.map l ~f:helper)
    | _ -> sexp
  in match Sexplib.Sexp.parse expr with
     | Done (sexp, _) -> Sexp.to_string_hum (helper (sexp))
     | _ -> raise (Internal_Exn "Incomplete sexp encountered!")
