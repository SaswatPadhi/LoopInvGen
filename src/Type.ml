open Exceptions

type t = INT
       | BOOL
       | CHAR
       | STRING
       | LIST
       [@@deriving sexp]

let of_string (s : string) : t =
  match s with
  | "Int"    -> INT
  | "Bool"   -> BOOL
  | "Char"   -> CHAR
  | "String" -> STRING
  | "List"   -> LIST
  | _ -> raise (Parse_Exn ("Could not parse type `" ^ s ^ "`."))
[@@inline always]

let to_string (t : t) : string =
  match t with
  | INT    -> "Int"
  | BOOL   -> "Bool"
  | CHAR   -> "Char"
  | STRING -> "String"
  | LIST   -> "List"
[@@inline always]
