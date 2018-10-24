open Base

open Exceptions

type t = INT
       | BOOL
       | LIST of t
       | TVAR of string
       [@@deriving compare,sexp]

let of_string (s : string) : t =
  match s with
  | "Int" -> INT
  | "Bool" -> BOOL
  | _ -> raise (Parse_Exn ("Could not parse type `" ^ s ^ "`."))

let rec to_string (t : t) : string =
  match t with
  | INT -> "Int"
  | BOOL -> "Bool"
  | LIST t -> "List(" ^ to_string t ^ ")"
  | TVAR t -> "TVar(" ^ t ^ ")"

let is_list (t : t) : bool =
  match t with
  | LIST _ -> true
  | _ -> false

let is_tvar (t : t) : bool =
  match t with
  | TVAR _ -> true
  | _ -> false