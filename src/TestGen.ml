open Core
open Core.Quickcheck

let for_type (t : Type.t) : Value.t Generator.t =
  let open Generator in
  match t with
  (* Full range of Int:
  | Type.INT -> Int.gen >>= fun i -> singleton (Value.Int i) *)
  | Type.INT -> (For_int.gen_incl (-4096) 4095) >>= fun i -> singleton (Value.Int i)
  | Type.BOOL -> Bool.gen >>= fun b -> singleton (Value.Bool b)
  | Type.CHAR -> Char.gen >>= fun c -> singleton (Value.Char c)
  | Type.STRING -> (For_int.gen_incl 0 64)
                   >>= fun len -> (String.gen_with_length len (Char.gen_print)
                                   >>= fun s -> singleton (Value.String s))
  | Type.LIST -> raise (Exceptions.Internal_Exn "Generators for List type not implemented!")
