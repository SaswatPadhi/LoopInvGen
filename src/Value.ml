open Base

open Exceptions

module T = struct
  type t = Int of int
         | Bool of bool
         | String of string
         [@@deriving compare,sexp]
end

include T
include Comparable.Make (T)

let typeof (v : t) : Type.t =
  match v with
  | Int _    -> Type.INT
  | Bool _   -> Type.BOOL
  | String _ -> Type.STRING
[@@inline always]

let to_string (v : t) : string =
  match v with
  | Int i    -> Int.to_string i
  | Bool b   -> Bool.to_string b
  | String s -> "\"" ^ s ^ "\""
[@@inline always]

let of_string (s : string) : t =
  try
    String (String.chop_prefix_exn ~prefix:"\"" (String.chop_suffix_exn s ~suffix:"\""))
  with Invalid_argument _ -> try
    Bool (Bool.of_string s)
  with Invalid_argument _ -> try
    Int (Int.of_string s)
  with Failure _ ->
    raise (Parse_Exn ("Failed to parse value `" ^ s ^ "`."))