open Core
open Core.Quickcheck
open Exceptions
open Types

let typ_gen (t : typ) : value Generator.t =
  let open Generator in
  match t with
  (* Use Small Ints: *)
  | TInt -> (For_int.gen_incl (-65536) 65535) >>= fun i -> singleton (VInt i)
  (* Full range of Int:
  | TInt -> Int.gen >>= fun i -> singleton (VInt i) *)
  | TBool -> Bool.gen >>= fun b -> singleton (VBool b)
  | _ -> raise (Invalid_Type_Exn ("Unknown type: " ^ (string_of_typ t)))

let typ_list_gen (ts : typ list) (pre : value list -> bool) : value list Generator.t =
  let open Generator in
  let t_gens = List.map ~f:typ_gen ts
  in create (
    fun ~size random ->
      let rec loopUntilFound () = begin
        let cand = List.map ~f:(fun g -> generate g ~size random) t_gens
        in if pre cand then cand else loopUntilFound ()
      end in loopUntilFound ())