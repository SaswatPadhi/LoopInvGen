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
}

type t = {
  logic : string ;
  inv_vars : var list ;
  inv'_vars : var list ;
  state_vars : var list ;
  trans_vars : var list ;
  inv_name : string ;
  pre : func ;
  trans : func ;
  post : func ;
  consts : value list ;
}

let value_assignment_constraints ?(negate = false)
                                 : var list -> value list -> string list =
  List.map2_exn ~f:(fun (name, _) value -> (
                      (if negate then "(not " else "") ^
                      "(= " ^ name ^ " " ^
                      (serialize_value value) ^ ")" ^
                      (if negate then ")" else "")))

let shrink_vars (s : t) : t =
  let (t_vars , s_vars) =
    List.(partition_tf (dedup (s.pre.args @ s.trans.args @ s.post.args))
                       ~f:(fun (v, _) -> String.is_suffix v ~suffix:"!"))
  in let filter_on vars = List.(filter ~f:(mem ~equal:(=) vars))
  in { s with
         inv_vars = filter_on s_vars s.inv_vars ;
         state_vars = filter_on s_vars s.state_vars ;
         trans_vars = filter_on t_vars s.trans_vars ;
         inv'_vars = List.filter_map s.inv'_vars
           ~f:(fun ((v, t) as iv) ->
                 if List.mem ~equal:(=) t_vars iv then Some iv
                 else let s = String.chop_suffix_exn v ~suffix:"!"
                       in if List.mem ~equal:(=) s_vars (s, t)
                          then Some (s, t) else None)
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
  | List((Atom op) :: fargs)
    -> let (args , consts) =
         List.fold fargs ~init:([],[])
                   ~f:(fun (args, consts) farg ->
                         let (a, c) = extract_args_and_consts vars farg
                         in ((a @ args), (c @ consts)))
       in List.((dedup args) , (dedup consts))

let load_var_usage (sexp : Sexp.t) : var =
  match sexp with
  | List([Atom(v) ; Atom(t)]) -> (v, (to_typ t))
  | _ -> raise (Parse_Exn ("Invalid variable usage: " ^ (Sexp.to_string_hum sexp)))

let load_define_fun lsexp : func * value list =
  match lsexp with
  | [Atom(name) ; List(args) ; _ ; expr]
    -> let args = List.map ~f:load_var_usage args in
       let (args, consts) = extract_args_and_consts args expr
       in ({ name = name ; expr = (Sexp.to_string_hum expr) ; args = args },
           consts)
  | _ -> raise (Parse_Exn ("Invalid function definition: "
                          ^ (Sexp.to_string_hum (List(Atom("define-fun") :: lsexp)))))

let load chan : t =
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
     in consts := List.dedup (!consts)
      ; Log.debug (lazy ("Variables in state: "
                        ^ (String.concat ~sep:", " state_var_names)))
      ; Log.debug (lazy ("Variables in invariant: "
                        ^ (List.to_string_map ~sep:", " ~f:fst (!inv_vars))))
      ; Log.debug (lazy ("Detected Constants: "
                        ^ (serialize_values ~sep:", " (!consts))))
      ; let s =
          shrink_vars {
            logic = !logic ;
            inv_vars = !inv_vars ;
            inv'_vars = List.map (!inv_vars) ~f:(fun (n, t) -> (n ^ "!", t)) ;
            state_vars = !state_vars ;
            trans_vars = !trans_vars ;
            inv_name = !inv_name ;
            pre = List.find_exn ~f:(fun f -> f.name = !pre_name) (!funcs) ;
            trans = List.find_exn ~f:(fun f -> f.name = !trans_name) (!funcs) ;
            post = List.find_exn ~f:(fun f -> f.name = !post_name) (!funcs) ;
            consts = !consts ;
          }
       in Log.debug (lazy ("Final variables in state: "
                     ^ (List.to_string_map ~sep:", " ~f:fst (s.state_vars))))
        ; Log.debug (lazy ("Final variables in invariant: "
                          ^ (List.to_string_map ~sep:", " ~f:fst (s.inv_vars))))
        ; Log.debug (lazy ("Final variables in trans: "
                          ^ (List.to_string_map ~sep:", " ~f:fst (s.trans_vars))))
        ; s