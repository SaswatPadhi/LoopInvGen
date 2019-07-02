open Base

open Exceptions

module T = struct
  type t = Int of int
         | Bool of bool
         | Char of char
         | String of string
         | List of t list
         | Array of (t * t) list * t
         [@@deriving compare,sexp]
end

include T
include Comparable.Make (T)

let rec typeof : t -> Type.t = function
  | Int _    -> Type.INT
  | Bool _   -> Type.BOOL
  | Char _   -> Type.CHAR
  | String _ -> Type.STRING
  | List _   -> Type.LIST  
  | Array  ((k,v) :: _, _) -> Type.ARRAY ((typeof k),(typeof v))
  | Array  ([], _) -> raise (Internal_Exn "Empty array not implemented!")

let to_string : t -> string = function
  | Int i    -> Int.to_string i
  | Bool b   -> Bool.to_string b
  | Char c   -> "\'" ^ (Char.to_string c) ^ "\'"
  | String s -> "\"" ^ s ^ "\""
  | List _   -> raise (Internal_Exn "List type (de/)serialization not implemented!")
  | Array (_, _)   -> raise (Internal_Exn "Array type (de/)serialization not implemented!")

let of_atomic_string (s : string) : t =
  try    
    Int (Int.of_string s)
  with Failure _ -> try
    Bool (Bool.of_string s)
  with Invalid_argument _ -> try
    Char (Char.of_string (String.(chop_suffix_exn ~suffix:"\'"
                                    (chop_prefix_exn ~prefix:"\'" s))))
  with Invalid_argument _ -> try
    String String.(chop_suffix_exn ~suffix:"\"" (chop_prefix_exn ~prefix:"\"" s))
  with Invalid_argument _ ->
    raise (Parse_Exn ("Failed to parse value `" ^ s ^ "`."))

let rec parse_ite (acc: (t*t) list) (sexp: Sexp.t) : t = 
let open Sexp in 
match sexp with  
  |Atom v ->         
        Array (acc, (of_atomic_string v))
  | List([Atom("ite");index;Atom(v);default])  ->                       
                      match index with 
                          | List([ _; _; Atom(v)]) ->                                     
                                    Array (acc, (parse_ite ([((of_atomic_string v),(of_atomic_string v))]@acc) default)) 
                          |  List([ _; _; List([(Atom "-") ; (Atom v)])]) ->                                    
                                    Array (acc, (parse_ite ([((of_atomic_string ("-" ^ v)),(of_atomic_string v))]@acc) default))                       
  | List ([]) -> Array ([],(Int 0))

let rec of_string (sexp: Sexp.t) : t =  
  let open Sexp in    
  match sexp with
      | Atom v -> (of_atomic_string v)
      | List([(Atom "-") ; (Atom v)]) -> (of_atomic_string ("-" ^ v))      
      | List([(Atom "lambda") ; List([ param ]) ; exp ]) ->  (parse_ite [] exp)      
      | _ -> raise (Internal_Exn ("Unable to deserialize value: "
                                ^ (to_string_hum sexp)))