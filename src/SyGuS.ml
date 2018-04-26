open Components
open Core
open Exceptions
open Sexplib.Sexp
open Types
open Utils

type func = {
  name : string ;
  expr : string ;
  args : var list ;
  return : typ ;
}

type t = {
  logic : string ;
  all_inv_vars : var list ;
  inv_vars : var list ;
  state_vars : var list ;
  trans_vars : var list ;
  inv_name : string ;
  funcs : func list ;
  pre : func ;
  trans : func ;
  post : func ;
  consts : value list ;
}

let value_assignment_constraint ?(negate = false) (vars : var list)
                                (vals : value list) : string =
  (if negate then "(not (and " else "(and ") ^
  (List.to_string_map2 vars vals ~sep:" "
                       ~f:(fun (name, _) value ->
                             ("(= " ^ name ^ " "
                             ^ (serialize_value value) ^ ")"))) ^
  (if negate then "))" else ")")

let shrink_vars (s : t) : t =
  let s_vars =
    List.(dedup_and_sort ~compare:Poly.compare
      (map (dedup_and_sort ~compare:Poly.compare
                           (s.pre.args @ s.trans.args @ s.post.args))
          ~f:(fun (v, t) -> match String.chop_suffix v ~suffix:"!" with
                            | Some v' -> (v', t)
                            | _ -> (v, t))))
  in let t_vars = List.map s_vars ~f:(fun (s, t) -> (s ^ "!", t))
  in let filter_on vars = List.(filter ~f:(mem ~equal:(=) vars))
  in { s with
         all_inv_vars = s.inv_vars ;
         inv_vars = filter_on s_vars s.inv_vars ;
         state_vars = filter_on s_vars s.state_vars ;
         trans_vars = filter_on t_vars s.trans_vars ;
     }

let rec extract_args_and_consts (vars : var list) (exp : Sexp.t)
                                : (var list) * (value list) =
  let open List in
  match exp with
  | List([]) | List((List _) :: _)
    -> raise (Internal_Exn ("Invalid function sexp: " ^ (Sexp.to_string_hum exp)))
  | (Atom a) | List([Atom a])
    -> begin match findi vars (fun _ (v, _) -> v = a) with
        | None -> ([], [Option.value_exn (Types.deserialize_value a)])
        | Some (_, v) -> ([v], [])
       end
  (* FIXME: Handling let expressins needs  more work:
     let in SyGuS format looks like (let ((<symb> <sort> <term>)+) <term>),
     but in Z3 the syntax is (let ((<symb> <term>)+) <term>).

  | List [(Atom "let") ; (List let_bindings) ; let_expr]
    -> let (bind_vars, args_in_bind , consts_in_bind) =
         List.fold let_bindings ~init:([],[],[])
                   ~f:(fun[@warning "-8"] (symbs, args, consts) (List [(Atom l_symb) ; (Atom l_typ) ; l_term]) ->
                         let (a, c) = extract_args_and_consts vars l_term
                         in (((l_symb, (to_typ l_typ)) :: symbs), (a @ args), (c @ consts)))
       in let (args , consts) = extract_args_and_consts (bind_vars @ vars) let_expr
       in let args = List.(filter args ~f:(fun a -> not (mem ~equal:Poly.equal bind_vars a)))
       in List.((dedup_and_sort ~compare:Poly.compare (args @ args_in_bind)),
                (dedup_and_sort ~compare:Poly.compare (consts @ consts_in_bind))) *)
  | List((Atom op) :: fargs)
    -> let (args , consts) =
         List.fold fargs ~init:([],[])
                   ~f:(fun (args, consts) farg ->
                         let (a, c) = extract_args_and_consts vars farg
                         in ((a @ args), (c @ consts)))
       in List.((dedup_and_sort ~compare:Poly.compare args),
                (dedup_and_sort ~compare:Poly.compare consts))

let load_var_usage (sexp : Sexp.t) : var =
  match sexp with
  | List([Atom(v) ; Atom(t)]) -> (v, (to_typ t))
  | _ -> raise (Parse_Exn ("Invalid variable usage: " ^ (Sexp.to_string_hum sexp)))

let load_define_fun lsexp : func * value list =
  match lsexp with
  | [Atom(name) ; List(args) ; Atom(r_typ) ; expr]
    -> let args = List.map ~f:load_var_usage args in
       let (args, consts) = extract_args_and_consts args expr
       in ({ name = name ; expr = (Sexp.to_string_hum expr) ; args = args ; return = (to_typ r_typ) },
           consts)
  | _ -> raise (Parse_Exn ("Invalid function definition: "
                          ^ (Sexp.to_string_hum (List(Atom("define-fun") :: lsexp)))))

let build_inv_func (inv : string) ~(sygus : t) : string =
  "(define-fun " ^ sygus.inv_name ^ " ("
  ^ (List.to_string_map
       sygus.all_inv_vars ~sep:" "
       ~f:(fun (v, t) -> "(" ^ v ^ " " ^ (Types.string_of_typ t) ^ ")"))
  ^ ") Bool " ^ inv ^ ")"

let load ?(shrink = true) chan : t =
  let logic : string ref = ref "" in
  let inv_name : string ref = ref "" in
  let pre_name : string ref = ref "" in
  let trans_name : string ref = ref "" in
  let post_name : string ref = ref "" in
  let inv_vars : var list ref = ref [] in
  let state_vars : var list ref = ref [] in
  let trans_vars : var list ref = ref [] in
  let funcs : func list ref = ref [] in
  let consts : value list ref = ref [] in
    List.iter
      ~f:(fun sexp ->
            match sexp with
            | List([Atom("check-synth")]) -> ()
            | List([Atom("set-logic"); Atom(l)])
              -> if !logic = "" then logic := l
                else raise (Parse_Exn ("Logic already set to: " ^ (!logic)))
            | List([Atom("synth-inv") ; Atom(invf) ; List(vars)])
              -> inv_name := invf ; inv_vars := List.map ~f:load_var_usage vars
            | List([Atom("declare-var"); Atom(v) ; Atom(t)])
              -> state_vars := (v, (to_typ t)) :: (!state_vars)
            | List([Atom("declare-primed-var") ; Atom(v) ; Atom(t)])
              -> state_vars := (v, (to_typ t)) :: (!state_vars)
               ; trans_vars := ((v ^ "!"), (to_typ t)) :: (!trans_vars)
            | List(Atom("define-fun") :: lsexp)
              -> let (func, fconsts) = load_define_fun lsexp
                  in funcs := func :: (!funcs) ; consts := fconsts @ (!consts)
            | List([Atom("inv-constraint") ; Atom(invf) ; Atom(pref)
                                          ; Atom(transf) ; Atom(postf) ])
              -> pre_name := pref ; trans_name := transf ; post_name := postf
            | _ -> raise (Parse_Exn ("Unknown command: " ^ (Sexp.to_string_hum sexp)))
         )
      (input_rev_sexps chan)
  ; let state_var_names = List.map ~f:fst (!state_vars)
     in consts := List.dedup_and_sort ~compare:Poly.compare (!consts)
      ; Log.debug (lazy ("Variables in state: "
                        ^ (String.concat ~sep:", " state_var_names)))
      ; Log.debug (lazy ("Variables in invariant: "
                        ^ (List.to_string_map ~sep:", " ~f:fst (!inv_vars))))
      ; Log.debug (lazy ("Detected Constants: "
                        ^ (serialize_values ~sep:", " (!consts))))
      ; let s = {
            logic = !logic ;
            all_inv_vars = !inv_vars ;
            inv_vars = !inv_vars ;
            state_vars = !state_vars ;
            trans_vars = !trans_vars ;
            inv_name = !inv_name ;
            funcs = !funcs ;
            pre = List.find_exn ~f:(fun f -> f.name = !pre_name) (!funcs) ;
            trans = List.find_exn ~f:(fun f -> f.name = !trans_name) (!funcs) ;
            post = List.find_exn ~f:(fun f -> f.name = !post_name) (!funcs) ;
            consts = !consts ;
          }
       in let s = (if shrink then (shrink_vars s) else s)
       in Log.debug (lazy ("Final variables in state: "
                     ^ (List.to_string_map ~sep:", " ~f:fst (s.state_vars))))
        ; Log.debug (lazy ("Final variables in invariant: "
                          ^ (List.to_string_map ~sep:", " ~f:fst (s.inv_vars))))
        ; Log.debug (lazy ("Final variables in trans: "
                          ^ (List.to_string_map ~sep:", " ~f:fst (s.trans_vars))))
        ; s