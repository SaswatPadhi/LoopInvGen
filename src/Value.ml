open Base

open Exceptions

module T = struct
  type t = Int of int
         | Bool of bool
         [@@deriving compare,sexp]
end

include T
include Comparable.Make (T)

let typeof (v : t) : Type.t =
  match v with
  | Int(_)   -> Type.INT
  | Bool(_)  -> Type.BOOL

let to_string (v : t) : string =
  match v with
  | Int(i)   -> Int.to_string i
  | Bool(b)  -> Bool.to_string b

let of_string (s : string) : t =
  try
    Bool (Bool.of_string s)
  with Invalid_argument _ -> try
    Int (Int.of_string s)
  with Failure _ ->
    raise (Parse_Exn ("Failed to parse value `" ^ s ^ "`."))

let of_int i = (Int i)
let to_int v =
  match v with
  | Int(i) -> i
  | _ -> raise (Parse_Exn ("Failed to parse `" ^ (to_string v) ^ "` as `int`."))

let of_bool b = (Bool b)
let to_bool v =
  match v with
  | Bool(b) -> b
  | _ -> raise (Parse_Exn ("Failed to parse `" ^ (to_string v) ^ "` as `bool`."))