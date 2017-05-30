open Components
open Core
open Exceptions
open Sexplib.Sexp
open Types

type sygusF = {
  name : string ;
  sexp : Sexp.t ;
  args : string list ;
  func : (value list -> value) ;
}

type sygus = {
  logic : string ;
  inv_vars : var list ;
  state_vars : var list ;
  trans_vars : var list ;
  inv_name : string ;
  pre : sygusF ;
  trans : sygusF ;
  post : sygusF ;
  consts : value list ;
}

let vars_to_string ?sep:(sep="\t") ?inv_only:(inv=true) (s : sygus) : string =
  String.concat ~sep (List.map ~f:fst (if inv then s.inv_vars else s.state_vars))

let state_to_string ?sep:(sep="\t") ?names:(names=true)
                    (s : sygus) (state : value list) : string =
  String.concat ~sep (List.map2_exn state s.state_vars
                                    ~f:(fun d (v, _) ->
                                          (if names then (v ^ ": ") else "") ^ (serialize_value d)))

(* TODO: Implement using z3's `ctx-solver-simplify` *)
let simplify_sexp_using_z3 (_ : var list) (exp : Sexp.t) : Sexp.t = exp

let rec scan_sexp_vars (vars : string list) (exp : Sexp.t) : string list =
  let open List in
  match exp with
  | List([]) | List((List _) :: _)
    -> raise (Internal_Exn ("Invalid function sexp: " ^ (Sexp.to_string_hum exp)))
  | (Atom a) | List([Atom a])
    -> (if mem ~equal:(=) vars a then [a] else [])
  | List((Atom op) :: args)
    -> let arg_vars = concat_map ~f:(scan_sexp_vars vars) args
       in List.dedup arg_vars

let rec sexp_to_func (vars : string list) (exp : Sexp.t) : (value list -> value) * value list =
  let open List in
  match exp with
  | List([]) | List((List _) :: _)
    -> raise (Internal_Exn ("Invalid function sexp: " ^ (Sexp.to_string_hum exp)))
  | (Atom a) | List([Atom a])
    -> let vo = deserialize_value a in
       begin match vo with
        | Some v -> ((fun largs -> v), [v])
        | None -> begin match findi ~f:(fun _ v -> v = a) vars with
                   | None -> raise (Parse_Exn ("Unknown identifier: " ^ a))
                   | Some (i,_) -> ((fun largs -> nth_exn largs i), [])
                  end
       end
  | List((Atom op) :: args)
    -> let all_components = Th_bool.components @ Th_lia.components in
       let fargs = map ~f:(sexp_to_func vars) args in
       let consts = concat_map ~f:snd fargs in
       let fargs = map ~f:fst fargs in
       let comp = find_exn ~f:(fun c -> c.name = op) all_components
       in ((fun largs -> comp.apply (map ~f:(fun f -> f largs) fargs)) , consts)

let build_func_on_state_vars (state_vars : string list) (f : sygusF) : sygusF =
  let pos = List.map ~f:(fun a -> match List.findi ~f:(fun _ v -> v = a) state_vars with
                                  | None -> raise (Parse_Exn ("Unknown identifier: " ^ a))
                                  | Some(i,_) -> i)
                     f.args
  in { name = f.name ; sexp = f.sexp ; args = state_vars
     ; func = (fun largs -> f.func (List.map ~f:(List.nth_exn largs) pos)) }

let load_var_usage sexp : var =
  match sexp with
  | List([Atom(v) ; Atom(t)]) -> (v, (to_typ t))
  | _ -> raise (Parse_Exn ("Invalid variable usage: " ^ (Sexp.to_string_hum sexp)))

let load_define_fun lsexp : sygusF * value list =
  match lsexp with
  | [Atom(name) ; List(arg_vars) ; _ ; exp]
    -> let vars = List.map ~f:load_var_usage arg_vars in
       let exp = simplify_sexp_using_z3 vars exp in
       let vars = scan_sexp_vars (List.map ~f:fst vars) exp in
       let (func, consts) = sexp_to_func vars exp
       in ({name = name ; sexp = exp ; args = vars ; func = func}, consts)
  | _ -> raise (Parse_Exn ("Invalid function definition: "
                          ^ (Sexp.to_string_hum (List(Atom("define-fun") :: lsexp)))))

let load chan : sygus =
  let logic : string ref = ref "" in
  let inv_name : string ref = ref "" in
  let pre_name : string ref = ref "" in
  let trans_name : string ref = ref "" in
  let post_name : string ref = ref "" in
  let inv_vars : var list ref = ref [] in
  let state_vars : var list ref = ref [] in
  let trans_vars : var list ref = ref [] in
  let funcs : sygusF list ref = ref [] in
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
    in consts := List.dedup (!consts) ;
       Log.debug (lazy ("Variables in state: " ^ (String.concat ~sep:", " state_var_names))) ;
       Log.debug (lazy ("Variables in invariant: " ^ (String.concat ~sep:", " (List.map ~f:fst (!inv_vars))))) ;
       Log.debug (lazy ("Detected Constants: " ^ (serialize_values ~sep:", " (!consts)))) ;
      {
        logic = !logic ;
        inv_vars = !inv_vars ;
        state_vars = !state_vars ;
        trans_vars = !trans_vars ;
        inv_name = !inv_name ;
        pre = build_func_on_state_vars state_var_names (List.find_exn ~f:(fun f -> f.name = !pre_name) (!funcs)) ;
        trans = List.find_exn ~f:(fun f -> f.name = !trans_name) (!funcs) ;
        post = build_func_on_state_vars state_var_names (List.find_exn ~f:(fun f -> f.name = !post_name) (!funcs)) ;
        consts = !consts ;
      }