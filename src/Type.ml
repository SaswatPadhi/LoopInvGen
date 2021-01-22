open Core

open Exceptions

module T = struct
  type t = INT
         | BOOL
         | CHAR
         | STRING
         | REAL
         | TVAR of string
         | LIST of t
         | ARRAY of (t * t)
         [@@deriving compare,sexp]
end

include T
include Comparable.Make (T)

let rec of_sexp (sexp: Sexp.t) : t =
  let open Sexp in
  match sexp with
    | Atom "Int"    -> INT
    | Atom "Bool"   -> BOOL
    | Atom "Char"   -> CHAR
    | Atom "String" -> STRING
    | Atom "Real"   -> REAL
    | List [Atom "List" ; typ]
      -> LIST (of_sexp typ)
    | List [Atom "Array" ; index ; value]
      -> ARRAY ((of_sexp index) , (of_sexp value))
    | s -> raise (Parse_Exn ("Could not parse type `" ^ (Sexp.to_string_hum s) ^ "`."))

let rec to_string : t -> string = function
  | INT         -> "Int"
  | BOOL        -> "Bool"
  | CHAR        -> "Char"
  | STRING      -> "String"
  | REAL        -> "Real"
  | LIST t      -> "(List " ^ (to_string t) ^ ")"
  | ARRAY (k,v) -> "(Array " ^ (to_string k) ^ " " ^ (to_string v) ^ ")"
  | TVAR n      -> n
    (* TODO: We may want to detect cases when a TVAR should never occur in a type,
             and throw exceptions in those cases *)

module Unification = struct
  (* Adapted from: https://eli.thegreenplace.net/2018/unification/
  *
  * TODO: The algorithm below is simple but not efficient.
  * See: https://eli.thegreenplace.net/2018/unification#efficiency
  *)

  let rec substitute_with_exn (env : (string * t) list) = function
    | TVAR name -> begin
        match List.find ~f:(fun (id,_) -> String.equal id name) env with
        | Some (_,value) -> value
        | _ -> raise (Unification_Exn ("Could not find a binding for " ^ name))
      end
    | LIST typ          -> LIST (substitute_with_exn env typ)
    | ARRAY (key,value) -> ARRAY ((substitute_with_exn env key),
                                  (substitute_with_exn env value))
    | t -> t

  let substitute (env : (string * t) list) (t : t) : t option =
    try Some (substitute_with_exn env t) with _ -> None

  let rec resolve_var ?(env = []) = function
    | lhs, TVAR rhs -> if String.equal lhs rhs
                       then raise (Unification_Exn "Circular dependency!")
                       else begin
                         match List.find env ~f:(fun (e,_) -> String.equal e rhs) with
                         | None -> (lhs, TVAR rhs)
                         | Some (_, (TVAR x)) -> resolve_var ~env (lhs, (TVAR x))
                         | Some (_, rhs) -> (lhs, rhs)
                       end
    | pair -> pair

  let rec of_var ?(env = []) (var : string) (rhs : t) =
    match List.Assoc.find env ~equal:String.equal var with
    | None -> begin
        match rhs with
        | TVAR var_rhs -> begin
            match List.Assoc.find env ~equal:String.equal var_rhs with
            | None -> List.fold ((var,rhs) :: env) ~init:[]
                                ~f:(fun acc elem -> (resolve_var elem ~env:(((var,rhs) :: env)) :: acc))
            | Some value -> of_type ~env (TVAR var) value
          end
        | _ -> List.fold ((var,rhs) :: env) ~init:[]
                         ~f:(fun acc elem -> (resolve_var elem ~env:(((var,rhs)::env)) :: acc))
      end
    | Some value -> of_type ~env value rhs
  and of_type ?(env = []) (lhs : t) (rhs : t) =
    match lhs, rhs with
    | TVAR x , _ -> of_var ~env x rhs
    | _ , TVAR y -> of_var ~env y lhs
    | LIST lhs_type, LIST rhs_type
      -> of_type lhs_type rhs_type ~env
    | ARRAY (lhs_key,lhs_value), ARRAY (rhs_key,rhs_value)
      -> let env = env @ (of_type ~env lhs_key rhs_key)
          in (of_type lhs_value rhs_value ~env)
    | lhs , rhs -> if equal lhs rhs then env
                   else raise (Unification_Exn "Circular dependency!")

  let rec of_types_exn ?(env = []) (lhs : t list) (rhs : t list) : (string * t) list =
    match lhs , rhs with
    | (x :: tx, y :: ty) -> of_types_exn ~env:(of_type ~env x y) tx ty
    | _ -> env

  let of_types ?(env = []) (t1 : t list) (t2 : t list) : (string * t) list option =
      try Some (of_types_exn t1 t2) with _ -> None
end
