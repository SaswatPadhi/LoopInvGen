open Core
open Exceptions

type t = INT
       | BOOL
       | CHAR
       | STRING
       | LIST
       | TVAR of string
       | ARRAY of (t * t)
       [@@deriving compare,sexp]

let rec of_sexp (sexp: Sexp.t) : t = 
  let open Sexp in
  match sexp with
    | Atom "Int"    -> INT
    | Atom "Bool"   -> BOOL
    | Atom "Char"   -> CHAR
    | Atom "String" -> STRING
    | Atom "List"   -> LIST
    | List [Atom "Array" ; index ; value]
      -> ARRAY ((of_sexp index) , (of_sexp value))
    | s -> raise (Parse_Exn ("Could not parse type `" ^ (Sexp.to_string_hum s) ^ "`."))

let rec to_string : t -> string = function
  | INT         -> "Int"
  | BOOL        -> "Bool"
  | CHAR        -> "Char"
  | STRING      -> "String"
  | LIST        -> "List"
  | ARRAY (a,b) -> "(Array" ^ " " ^ (to_string a) ^ " " ^ (to_string b) ^ ")"
  | TVAR (a)    -> raise (Internal_Exn ("Attempted to serialize a type variable."))
