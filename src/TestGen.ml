open Core
open Core.Quickcheck

let for_type (t : Type.t) : Value.t Generator.t =
  let open Generator in
  match t with
  (* Use Small Ints, within 2^12: *)
  | Type.INT -> (For_int.gen_incl (-4096) 4095) >>= fun i -> singleton (Value.Int i)
  (* Full range of Int:
  | Type.INT -> Int.gen >>= fun i -> singleton (Value.Int i) *)
  | Type.BOOL -> Bool.gen >>= fun b -> singleton (Value.Bool b)