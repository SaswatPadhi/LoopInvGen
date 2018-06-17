open Base

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

let value_compare (v1: value) (v2: value) =
  match (v1, v2) with
  | (VInt i1), (VInt i2) -> Int.compare i1 i2
  | (VBool b1), (VBool b2) -> Bool.compare b1 b2
  | _ -> Poly.compare v1 v2

type program =
  | FCall of string * program list
  | Const of value
  | Var of string

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
  if Poly.equal t TInt then
    try Some (VInt (Int.of_string s)) with _ -> None
  else if Poly.equal t TBool then
    try Some (VBool (Bool.of_string s)) with _ -> None
  else None

let deserialize_value (s : string) : value option =
  if String.equal s "-<ERROR>-" then Some VError
  else if String.equal s "-<UNKNOWN>-" then Some VDontCare
  else try
    Some (VBool (Bool.of_string s))
  with Invalid_argument _ -> try
    Some (VInt (Int.of_string s))
  with Failure _ ->
    None

let deserialize_values ?(sep = '\t') (s : string) : value option list =
  List.map (String.split ~on:sep s) ~f:deserialize_value

let serialize_value (v : value) : string =
  match v with
  | VInt(i)      -> Int.to_string i
  | VBool(b)     -> Bool.to_string b
  | VError       -> "-<ERROR>-"
  | VDontCare    -> "-<UNKNOWN>-"

let serialize_values ?(sep = "\t") (vs : value list) : string =
  String.concat ~sep (List.map vs ~f:serialize_value)

let print_data chan (data : value) : unit =
  Stdio.Out_channel.output_string chan (serialize_value data)