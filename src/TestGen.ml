open Core
open Quickcheck
open Generator

let rec for_type (t : Type.t) : Value.t Generator.t =
  match t with
  (* Full range of Int:
  | Type.INT -> Int.gen >>= fun i -> singleton (Value.Int i) *)
  | Type.INT -> (Int.gen_incl (-4096) 4095) >>= fun i -> singleton (Value.Int i)
  | Type.BOOL -> bool >>= fun b -> singleton (Value.Bool b)
  | Type.CHAR -> char >>= fun c -> singleton (Value.Char c)
  | Type.STRING -> (Int.gen_incl 0 64)
                  >>= fun len -> (String.gen_with_length len (Char.gen_print)
                                  >>= fun s -> singleton (Value.String s))
  | Type.LIST -> raise (Exceptions.Internal_Exn "Generators for List type not implemented!")
  | Type.ARRAY (key,value) -> (Int.gen_incl 0 64)
                              >>= fun len -> ((tuple2 (List.gen_with_length len (tuple2 (for_type key) (for_type value))) (for_type value))
                                              >>= fun (arr, def) -> singleton (Value.Array (key, value, arr, def)))
  | Type.TVAR _ -> raise (Exceptions.Internal_Exn "Generators for TVAR type not implemented!")
