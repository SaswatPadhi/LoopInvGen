open Exceptions
open Core

type t = INT
       | BOOL
       | CHAR
       | STRING
       | LIST
       | ARRAY of (t * t)
       [@@deriving sexp]

let rec of_string : string -> t = function
  | "Int"    -> INT
  | "Bool"   -> BOOL
  | "Char"   -> CHAR
  | "String" -> STRING
  | "List"   -> LIST   
  | s -> 
        match (String.split s ~on:' ') with
        | ["Array";index;value] -> ARRAY ((of_string index), (of_string value))
        | _ ->raise (Parse_Exn ("Could not parse type `" ^ s ^ "`."))
        (* ARRAY (of_string (String.concat (" " index))),(of_string (String.concat (" " value))) *)
  (* | s  -> match Str.split (Str.regexp " ") s with 
                | ["Array";index;value] -> ARRAY ((of_string index),(of_string value))                                
                 *)
  (* | "Array" -> ARRAY ((of_string "Int"),(of_string "Int")) *)
  (* | s -> raise (Parse_Exn ("Could not parse type `" ^ s ^ "`.")) *)

let rec to_string : t -> string = function
  | INT    -> "Int"
  | BOOL   -> "Bool"
  | CHAR   -> "Char"
  | STRING -> "String"
  | LIST   -> "List"
  | ARRAY (a,b) -> "(Array" ^ " " ^(to_string a) ^ " " ^ (to_string b) ^ ")"
