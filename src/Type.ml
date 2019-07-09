open Exceptions
open Core

type t = INT
       | BOOL
       | CHAR
       | STRING
       | LIST
       | ARRAY of (t * t)       
       [@@deriving sexp]

let of_atomic_string (s:string) : t = 
  match s with 
  | "Int"    -> INT
  | "Bool"   -> BOOL
  | "Char"   -> CHAR
  | "String" -> STRING
  | "List"   -> LIST    
  | _ -> raise (Parse_Exn ("Could not parse type `" ^ s ^ "`."))  

let rec of_string (sexp: Sexp.t) : t =          
  match sexp with
    | Sexp.(Atom v) -> (of_atomic_string v)                  
    | Sexp.(List ([Atom("Array");index;value])) -> ARRAY ((of_string (index)),(of_string (value)))
    | _ -> raise (Parse_Exn ("Could not parse type `" ^ (Sexp.to_string_hum sexp) ^ "`."))  
    

let rec to_string : t -> string = function
  | INT    -> "Int"
  | BOOL   -> "Bool"
  | CHAR   -> "Char"
  | STRING -> "String"
  | LIST   -> "List"
  | ARRAY (a,b) -> "(Array" ^ " " ^(to_string a) ^ " " ^ (to_string b) ^ ")"
