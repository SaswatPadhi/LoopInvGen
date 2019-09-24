open Base

open Exceptions

module T = struct
  type t = Int of int
         | Bool of bool
         | Char of char
         | String of string
         | List of Type.t * t list
         | Array of Type.t * Type.t * (t * t) list * t
           (* FIXME: Use HashTable instead of List *)
         [@@deriving compare,sexp]
end

include T
include Comparable.Make (T)

let rec typeof : t -> Type.t = function
  | Int _         -> Type.INT
  | Bool _        -> Type.BOOL
  | Char _        -> Type.CHAR
  | String _      -> Type.STRING
  | List (typ, _) -> Type.LIST typ
  | Array (key_type, value_type, _, _)
    -> Type.ARRAY (key_type,value_type)

let rec to_string : t -> string = function
  | Int i    -> Int.to_string i
  | Bool b   -> Bool.to_string b
  | Char c   -> "\'" ^ (Char.to_string c) ^ "\'"
  | String s -> "\"" ^ s ^ "\""
  | List _   -> raise (Internal_Exn "List type (de/)serialization not implemented!")
  | Array (key_type, val_type, value, default_v)
    -> let default_string = "((as const (Array " ^ (Type.to_string key_type) ^ " " ^ (Type.to_string val_type) ^ ")) " ^ (to_string default_v) ^ ")"
        in List.fold_left ~init:default_string value
                          ~f:(fun arr -> function (k,v) -> "(store " ^ arr ^ " " ^ (to_string k) ^ " " ^ (to_string v) ^ ")")

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

(* We assume that an array serialization provides explicit (k,v) pairs --
 * either using nested `store` calls, or if-then-else constructs.
 * The different array formats are described in more details here:
 * https://docs.google.com/document/d/1zSXs91eeJ1hc7bmcUTzeJtjiCHTNEYZKZpi_436HvbA
 *)
let rec parse_array (acc : (t*t) list) (sexp : Sexp.t) : Type.t * Type.t * (t*t) list * t =
  let open Sexp in
  match sexp with
  | List [ List [ Atom "as" ; Atom "const" ; List [Atom "Array" ; key_type ; val_type] ] ; def_val]
    -> ((Type.of_sexp key_type) , (Type.of_sexp val_type) , acc , (of_sexp def_val))
  | List [Atom "store" ; rest_of_array ; key ; value]
    -> parse_array (acc @ [ ((of_sexp key) , (of_sexp value)) ]) rest_of_array
  | _ -> raise (Parse_Exn ("Failed to parse value `" ^ (Sexp.to_string_hum sexp) ^ "`."))

and parse_ite (acc : (t*t) list) (sexp : Sexp.t) : (t*t) list * t =
  match sexp with
  | List[ Sexp.Atom "ite" ; List[ _ ; _ ; key ] ; value ; rest]
    -> parse_ite (acc @ [ ((of_sexp key) , (of_sexp value)) ]) rest
  | default -> (acc, (of_sexp default))

and [@warning "-8"] parse_named_array (sexp : Sexp.t)
                                      (List [List [name ; value]] : Sexp.t)
                                      (val_type : Sexp.t)
                                      : t =
  let key_name, key_type = name, (Type.of_sexp value) in
  let parsed_array, default = (parse_ite [] sexp)
   in Array (key_type, (Type.of_sexp val_type), parsed_array, default)

and of_sexp (sexp : Sexp.t) : t =
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

let of_string (s : string) : t =
  (of_sexp (Core.Sexp.of_string s))