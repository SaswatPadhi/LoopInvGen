open Base

open Exceptions

module T = struct
  type t = Int of int
         | Bool of bool
         | Char of char
         | String of string
         | List of t list
         | BitVec of int*int
         [@@deriving compare,sexp]
end

include T
include Comparable.Make (T)

let typeof : t -> Type.t = function
  | Int _    -> Type.INT
  | Bool _   -> Type.BOOL
  | Char _   -> Type.CHAR
  | String _ -> Type.STRING
  | List _   -> Type.LIST
  | BitVec (n, _) -> Type.BITVEC n

let to_string : t -> string = function
  | Int i    -> Int.to_string i
  | Bool b   -> Bool.to_string b
  | Char c   -> "\'" ^ (Char.to_string c) ^ "\'"
  | String s -> "\"" ^ s ^ "\""
  | List _   -> raise (Internal_Exn "List type (de/)serialization not implemented!")
  | BitVec _ -> raise (Internal_Exn "BitVec type (de/)serialization not implemented!")

let of_string (s : string) : t =
  try
    Int (Int.of_string s)
  with Failure _ -> try
    Bool (Bool.of_string s)
  with Invalid_argument _ -> try
    Char (Char.of_string (String.(chop_suffix_exn ~suffix:"\'"
                                    (chop_prefix_exn ~prefix:"\'" s))))
  with Invalid_argument _ -> try
      String String.(chop_suffix_exn ~suffix:"\"" (chop_prefix_exn ~prefix:"\"" s))
    with Invalid_argument _ -> try
        String s
  with Invalid_argument _ ->
    raise (Parse_Exn ("Failed to parse value `" ^ s ^ "`."))
          (* TODO: Implement BitVec from string. *)
