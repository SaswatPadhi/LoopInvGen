open Core

open Exceptions

module T = struct
  type t = INT
         | BOOL
         | CHAR
         | STRING
         | TVAR of string
         | LIST of t
         | ARRAY of (t * t)
         | BITVEC of int
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
    | List [Atom "List" ; typ]
      -> LIST (of_sexp typ)
    | List [Atom "Array" ; index ; value]
      -> ARRAY ((of_sexp index) , (of_sexp value))
    | List [Atom "_"; Atom "BitVec"; Atom n]
      -> BITVEC (Int.of_string n)
    | s -> raise (Parse_Exn ("Could not parse type `" ^ (Sexp.to_string_hum s) ^ "`."))

let rec to_string : t -> string = function
  | INT         -> "Int"
  | BOOL        -> "Bool"
  | CHAR        -> "Char"
  | STRING      -> "String"
  | LIST t      -> "(List " ^ (to_string t) ^ ")"
  | ARRAY (k,v) -> "(Array " ^ (to_string k) ^ " " ^ (to_string v) ^ ")"
  | BITVEC n    -> "(_ BitVec " ^ (Int.to_string n) ^ ")"
  | TVAR n      -> n
    (* TODO: We may want to detect cases when a TVAR should never occur in a type,
             and throw exceptions in those cases *)

module Unification = struct
  (* Adapted from: https://eli.thegreenplace.net/2018/unification/
  *
  * TODO: The algorithm below is simple but not efficient.
  * See: https://eli.thegreenplace.net/2018/unification#efficiency
  *)
  type id =
    | STR of string
    | NUM of int

  let rec substitute_with_exn (env : (id * t) list) = function
    | TVAR name -> begin
        match List.find ~f:(fun (id,_) -> match id with
                                          | STR idstr -> String.equal idstr name
                                          | _ -> false) env with
        | Some (_,value) -> value
        | _ -> raise (Unification_Exn ("Could not find a binding for " ^ name))
      end
    | LIST typ          -> LIST (substitute_with_exn env typ)
    | ARRAY (key,value) -> ARRAY ((substitute_with_exn env key),
                                  (substitute_with_exn env value))
    | BITVEC len        -> (match List.find env ~f:(fun (id,_) -> (match id with
                                                                   | NUM idnum -> Int.equal idnum len
                                                                   | _ -> false)) with
                            | Some (_, value) -> value
                            | _ -> raise (Unification_Exn ("Could not find a binding for " ^ (to_string (BITVEC len)))))
    | t -> t

  let substitute (env : (id * t) list) (t : t) : t option =
    try Some (substitute_with_exn env t) with _ -> None

  let rec resolve_var ?(env = []) = function
    | STR lhs, TVAR rhs -> if String.equal lhs rhs
                           then raise (Unification_Exn "Circular dependency!")
                           else begin
                               match List.find env ~f:(fun (e,_) -> match e with
                                                                    | STR idstr -> String.equal idstr rhs
                                                                    | _ -> false) with
                               | None -> (STR lhs, TVAR rhs)
                               | Some (_, (TVAR x)) -> resolve_var ~env (STR lhs, (TVAR x))
                               | Some (_, rhs) -> (STR lhs, rhs)
                             end
    | pair -> pair

  let rec of_var ?(env = []) (var : id) (rhs : t) =
    match List.Assoc.find env ~equal:(fun idquery idenv -> (match (idenv, idquery) with
                                                | (STR id1), (STR id2) -> String.equal id1 id2
                                                | (NUM id1), (NUM id2) -> Int.equal id1 id2
                                                | _ -> false)) var with
    | None -> begin
        match rhs with
        | TVAR var_rhs -> begin
            match List.Assoc.find env ~equal:(fun _ idvar -> match idvar with
                                                           | STR idstr -> String.equal idstr var_rhs
                                                           | _ -> false) (STR var_rhs) with
            | None -> List.fold ((var,rhs) :: env) ~init:[]
                                ~f:(fun acc elem -> (resolve_var elem ~env:(((var,rhs) :: env)) :: acc))
            | Some value -> (match var with
                            | STR varstr -> of_type ~env (TVAR varstr) value
                            | _ -> raise (Unification_Exn ("Type variable was as integer but should be a string")))
          end
        | _ -> List.fold ((var,rhs) :: env) ~init:[]
                         ~f:(fun acc elem -> (resolve_var elem ~env:(((var,rhs)::env)) :: acc))
      end
    | Some value -> of_type ~env value rhs
  and of_type ?(env = []) (lhs : t) (rhs : t) =
    match lhs, rhs with
    | TVAR x , _ -> of_var ~env (STR x) rhs
    | _ , TVAR y -> of_var ~env (STR y) lhs
    | LIST lhs_type, LIST rhs_type
      -> of_type lhs_type rhs_type ~env
    | ARRAY (lhs_key,lhs_value), ARRAY (rhs_key,rhs_value)
      -> let env = env @ (of_type ~env lhs_key rhs_key)
          in (of_type lhs_value rhs_value ~env)
    | BITVEC llen, BITVEC rlen -> (match llen, rlen with
                                   | _ when Int.(<) llen 0 -> of_var ~env (NUM llen) rhs
                                   | _ when Int.(<) rlen 0 -> of_var ~env (NUM rlen) lhs
                                   | _ -> env)
    | lhs , rhs -> if equal lhs rhs then env
                   else raise (Unification_Exn "Circular dependency!")

  let rec of_types_exn ?(env = []) (lhs : t list) (rhs : t list) : (id * t) list =
    match lhs , rhs with
    | (x :: tx, y :: ty) -> of_types_exn ~env:(of_type ~env x y) tx ty
    | _ -> env

  let of_types ?(env = []) (t1 : t list) (t2 : t list) : (id * t) list option =
      try Some (of_types_exn t1 t2) with _ -> None
end