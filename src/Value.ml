open Base

open Exceptions

module T = struct
  type t = Int of int
         | Bool of bool
         | Char of char
         | String of string
         | List of t list
         | Array of Type.t * Type.t * (t * t) list * t
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
  | Array  (key_type, value_type, _, _) -> Type.ARRAY (key_type,value_type)  

let rec to_string : t -> string = function
  | Int i    -> Int.to_string i
  | Bool b   -> Bool.to_string b
  | Char c   -> "\'" ^ (Char.to_string c) ^ "\'"
  | String s -> "\"" ^ s ^ "\""
  | List _   -> raise (Internal_Exn "List type (de/)serialization not implemented!")
  | Array (key_type, val_type, value, default_v)   ->                                                          
                            (let default_string = "((as const (Array "^ (Type.to_string key_type) ^" "^ (Type.to_string val_type) ^")) "^ (to_string default_v) ^")" in
                              List.fold_left ~f:(fun arr elem -> match elem with                             
                              | (key,value) -> "(store " ^ arr ^ " " ^ (to_string key)^ " "^(to_string value) ^")") ~init:default_string value)                                                                            

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
    
let rec parse_array (acc: (t*t) list) (sexp: Sexp.t) : Type.t * Type.t * (t*t) list *t =
match sexp with 
| List([Sexp.List([ Atom "as"; Atom "const"; Sexp.List([Atom "Array";key_type;val_type])]); Atom def_val]) -> ((Type.of_string key_type),(Type.of_string val_type),acc, (of_atomic_string def_val))
| List([Sexp.Atom "store"; rest_of_array; Sexp.Atom key; Sexp.Atom value]) -> (parse_array (acc@[((of_atomic_string key),(of_atomic_string value))]) rest_of_array) 
| List([Sexp.Atom "store"; rest_of_array; Sexp.Atom key; List([(Atom "-") ; (Atom v)])]) -> (parse_array (acc@[((of_atomic_string key),(of_atomic_string ("-" ^ v)))]) rest_of_array) 
| _ -> raise (Parse_Exn ("Failed to parse value `" ^ (Sexp.to_string_hum sexp) ^ "`."))

let rec of_string (sexp: Sexp.t) : t =  
  let open Sexp in      
  match sexp with      
      | Atom v -> (of_atomic_string v)
      | List([(Atom "-") ; (Atom v)]) -> (of_atomic_string ("-" ^ v))
      | List([List([ Atom "as"; Atom "const"; _ ]); _]) | List([Atom "store";_;_;_]) -> 
                                      (let key_type, val_type, arr,def_val = (parse_array [] sexp) in                                                                
                                                Array ((key_type) , (val_type) ,arr, def_val))            
      | List(Atom "let"::_) -> 
                            (let key_type, val_type, arr,def_val = (parse_array [] (Utils.remove_lets sexp)) in                                                                
                                      Array ((key_type) , (val_type) ,arr, def_val))                                       
      | _ -> raise (Internal_Exn ("Unable to deserialize value: "
                                ^ (to_string_hum sexp)))

