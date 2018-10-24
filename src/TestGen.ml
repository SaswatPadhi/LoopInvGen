open Core
open Core.Quickcheck

let (--) lower upper =
  For_int.gen_incl lower upper

let weighted lower upper =
  let open Quickcheck.Generator in
  weighted_union
  (List.map (List.range lower (upper + 1)) ~f:(fun x -> (float_of_int x, singleton x)))

let small_int = -4 -- 4
let small_weighted_nat = weighted 0 5

type setting = {
  list_dim : (int Generator.t) list;
  int_range : int Generator.t;
}

let default_setting = {
  list_dim = [];
  int_range = (-4096 -- 4095);
}

let rec for_type ?(s : setting = default_setting) (t : Type.t) : Value.t Generator.t =
  let open Generator in
  match t with
  (* Use Small Ints, within 2^12: *)
  | Type.INT -> s.int_range >>= fun i -> singleton (Value.Int i)
  (* Full range of Int:
  | Type.INT -> Int.gen >>= fun i -> singleton (Value.Int i) *)
  | Type.BOOL -> Bool.gen >>= fun b -> singleton (Value.Bool b)
  | Type.LIST t ->
    let (dim_hd, dim_tl) = match s.list_dim with
      | h :: t -> (h, t)
      | [] -> (small_weighted_nat, []) in
    let elem = for_type ~s:{s with list_dim=dim_tl} t in
    dim_hd
    >>= fun len -> List.gen_with_length len elem
    >>= fun res -> singleton (Value.List (res, t))
  | _ -> failwith "Not implemented"

let repeat ~n ?seed genlist =
  let open Generator in
  let gen = all genlist in
  let random_seed = match seed with
    | None -> `Nondeterministic
    | Some seed -> `Deterministic seed in
  random_value (list_with_length n gen) ~seed:random_seed