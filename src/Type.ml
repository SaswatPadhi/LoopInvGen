open Exceptions

type t = INT
       | BOOL
       | STRING
       [@@deriving sexp]

let of_string (s : string) : t =
  match s with
  | "Int"    -> INT
  | "Bool"   -> BOOL
  | "String" -> STRING
  | _ -> raise (Parse_Exn ("Could not parse type `" ^ s ^ "`."))

let to_string (t : t) : string =
  match t with
  | INT    -> "Int"
  | BOOL   -> "Bool"
  | STRING -> "String"