open Core_kernel
open Type
open Exceptions


let rec unifyvar (var : string) (rhs : t) (env: (string * t) list) =
  match List.Assoc.find env ~equal:String.equal var with
  | None ->
          (match rhs with 
            | TVAR var_rhs ->
            (match List.Assoc.find env ~equal:String.equal var_rhs with
                          | None -> List.fold ((var,rhs)::env) ~init:[] ~f:(fun acc elem -> (resolve elem ((var,rhs)::env))::acc)
                          | Some value -> (unification (TVAR var) value env))
            | _ -> List.fold ((var,rhs)::env) ~init:[] ~f:(fun accum elem -> (resolve elem ((var,rhs)::env))::accum))
  | Some value -> (unification value rhs env)
and resolve (curpair: (string * t)) (env: (string * t) list) =
  match curpair with
  | lhs, TVAR rhs -> if String.equal lhs rhs then raise (Internal_Exn "Impossible case!") else
                    begin match List.find env ~f:(fun (elemlhs,elemrhs) -> String.equal elemlhs rhs) with
                    | None -> curpair
                    | Some (_, frhs) -> begin match frhs with 
                                       | TVAR x -> (resolve (lhs,frhs) env)
                                       |_ -> (lhs,frhs)
                                 end
                    end
  | _ -> curpair
and unification (lhs: t) (rhs: t) (env: (string * t) list) =
  match lhs, rhs with
  | TVAR x , _ -> (unifyvar x rhs env)
  | _ , TVAR y -> (unifyvar y lhs env)
  | ARRAY (lhs_key, lhs_value), ARRAY (rhs_key, rhs_value) ->  let env = env@(unification lhs_key rhs_key env) in
                                                               (unification lhs_value rhs_value env)
  | lhs , rhs -> if Poly.equal lhs rhs then env else raise (Internal_Exn "Impossible case!")

let rec unify_types (lhs: t list) (rhs: t list) (env: (string * t) list): (string * t) list =
  match (lhs, rhs) with
  | (x :: tx, y :: ty) -> (let env = (unification x y env) in 
                                     (unify_types tx ty env))
  |_ -> env

let unify (t1 : t list) (t2 : t list) : (string * t) list option =
    try Some (unify_types t1 t2 []) with _ -> None

let is_unifiable lhs rhs = match unify lhs rhs with Some _ -> true | _ -> false
