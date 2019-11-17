open Base
open Exceptions

type t = INT
       | BOOL
       | CHAR
       | STRING
       | LIST
       | BITVEC of int
       [@@deriving sexp]

let of_string : string -> t = function
  | "Int"    -> INT
  | "Bool"   -> BOOL
  | "Char"   -> CHAR
  | "String" -> STRING
  | "List"   -> LIST
  (* | "BitVec" -> BITVEC *)
  | s -> raise (Parse_Exn ("Could not parse type `" ^ s ^ "`."))

let of_params : string * int -> t = function
  | "BitVec", n -> BITVEC n

let to_string : t -> string = function
  | INT    -> "Int"
  | BOOL   -> "Bool"
  | CHAR   -> "Char"
  | STRING -> "String"
  | LIST   -> "List"
  | BITVEC n -> "(_ BitVec " ^ (Int.to_string_hum n) ^ ")"
