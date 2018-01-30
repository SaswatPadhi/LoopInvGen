open Core
open Exceptions

type logic =
  | LLIA
  | LNIA

let string_of_logic (l : logic) : string =
  match l with
  | LLIA -> "LIA"
  | LNIA -> "NIA"

let logic_of_string (s : string) : logic =
  match s with
  | "LIA" -> LLIA
  | "NIA" -> LNIA
  | _ -> raise (Parse_Exn ("Unknown logic " ^ s))

type typ =
  | TInt
  | TBool
  | TUnknown

type var = string * typ

let to_typ (t : string) : typ =
  match t with 
  | "Int" -> TInt
  | "Bool" -> TBool
  | _ -> TUnknown

let string_of_typ (t : typ) : string =
  match t with 
  | TInt -> "Int"
  | TBool -> "Bool"
  | TUnknown -> "Unknown"

type value =
  | VInt of int
  | VBool of bool
  | VError
  | VDontCare

  type program =
    | Node of string * program list
    | Leaf of string

  type runnable = (string * (value list -> value)) * program

let typeof (v : value) : typ =
  match v with
  | VInt(_)     -> TInt
  | VBool(_)    -> TBool
  | _           -> TUnknown

let of_int i = (VInt i)
let of_bool b = (VBool b)

let vtrue = VBool true
let vfalse = VBool false

let from_int = function | VInt(i) -> i | _ -> raise (Internal_Exn "")
let from_bool = function | VBool(b) -> b | _ -> raise (Internal_Exn "")

let deserialize_value_to ~(t : typ) (s : string) : value option =
  if t = TInt then
    try Some (VInt (int_of_string s)) with _ -> None
  else if t = TBool then
    try Some (VBool (bool_of_string s)) with _ -> None
  else None

let deserialize_value (s : string) : value option =
  if s = "-<ERROR>-" then Some VError
  else if s = "-<UNKNOWN>-" then Some VDontCare
  else try
    Some (VBool (bool_of_string s))
  with Invalid_argument _ -> try
    Some (VInt (int_of_string s))
  with Failure _ ->
    None

let deserialize_values ?(sep = '\t') (s : string) : value option list =
  List.map (String.split ~on:sep s) ~f:deserialize_value

let serialize_value (v : value) : string =
  match v with
  | VInt(i)      -> string_of_int i
  | VBool(b)     -> string_of_bool b
  | VError       -> "-<ERROR>-"
  | VDontCare    -> "-<UNKNOWN>-"

let serialize_values ?(sep = "\t") (vs : value list) : string =
  String.concat ~sep (List.map vs ~f:serialize_value)

let rec print_data chan (data : value) : unit =
  Out_channel.output_string chan (serialize_value data)