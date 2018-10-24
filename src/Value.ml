open Base

open Exceptions

open Utils

module T = struct
  type t = Int of int
         | Bool of bool
         | List of t list * Type.t
         [@@deriving compare,sexp]
end

include T
include Comparable.Make (T)

let typeof (v : t) : Type.t =
  match v with
  | Int _  -> Type.INT
  | Bool _ -> Type.BOOL
  | List (_,t) -> Type.LIST t
[@@inline always]

let rec to_string (v : t) : string =
  match v with
  | Int i  -> Int.to_string i
  | Bool b -> Bool.to_string b
  | List (l, _) -> "(" ^ List.to_string_map l ~sep:" " ~f:to_string ^ ")"
[@@inline always]

let of_string (s : string) : t =
  try
    Bool (Bool.of_string s)
  with Invalid_argument _ -> try
    Int (Int.of_string s)
  with Failure _ ->
    raise (Parse_Exn ("Failed to parse value `" ^ s ^ "`."))