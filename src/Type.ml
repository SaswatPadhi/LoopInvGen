open Exceptions

type t = INT
       | BOOL
       | CHAR
       | STRING
       | LIST
       [@@deriving sexp]

let of_string : string -> t = function
  | "Int"    -> INT
  | "Bool"   -> BOOL
  | "Char"   -> CHAR
  | "String" -> STRING
  | "List"   -> LIST
  | s -> raise (Parse_Exn ("Could not parse type `" ^ s ^ "`."))

let to_string : t -> string = function
  | INT    -> "Int"
  | BOOL   -> "Bool"
  | CHAR   -> "Char"
  | STRING -> "String"
  | LIST   -> "List"
