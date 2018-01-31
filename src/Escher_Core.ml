open Types

type bin_tree =
  | BTLeaf of int
  | BTNode of int * bin_tree * bin_tree

let rec bt_height = function
  | BTLeaf _ -> 1
  | BTNode (_, left, right) -> 1 + (max (bt_height left) (bt_height right))

let rec bt_size = function
  | BTLeaf _ -> 1
  | BTNode (_, left, right) -> 1 + (bt_size left) + (bt_size right)

let rec bt_string = function
  | BTNode (x, left, right) ->
      "(" ^ (string_of_int x)
      ^ " " ^ (bt_string left)
      ^ " " ^ (bt_string right) ^ ")"
  | BTLeaf x -> string_of_int x

let rec program_string = function
  | FCall (x, args) -> "(" ^ x ^ " " ^ (String.concat " " (List.map program_string args)) ^ ")"
  | Const v -> serialize_value v
  | Var x -> x

let rec program_height = function
  | FCall (_, args) -> 1 + (List.fold_left max 0 (List.map program_height args))
  | Const _ -> 1
  | Var _ -> 1

let rec program_size = function
  | FCall (_, args) -> List.fold_left (+) 1 (List.map program_size args)
  | Const _ -> 1
  | Var _ -> 1

let value_lt x y = match x,y with
  | (VInt x, VInt y) -> x >= 0 && y >= 0 && x < y
  | (_, _) -> false

let value_leq x y = match x,y with
  | (VInt x, VInt y) -> x = y || x >= 0 && y >= 0 && x < y
  | (_, _) -> false

let varray_string values = serialize_values (Array.to_list values)

(* lexicographic ordering *)
let varray_lt x y =
  let len = Array.length x in
  let rec go i = (i < len)
              && (value_lt x.(i) y.(i)
                || (value_leq x.(i) y.(i) && go (i + 1)))
  in go 0

let vlist_lt x y = varray_lt (Array.of_list x) (Array.of_list y)

module Value = struct
  type t = value
  let compare = Pervasives.compare
end

module Program = struct
  type t = runnable
  let compare = Pervasives.compare
end

(* Subprogram with value vector *)
module Vector = struct
  type t = runnable * value array
  let compare x y = Pervasives.compare (snd x) (snd y)
  let string (((str, func),nodes), values) =
    str ^ " : " ^ (varray_string values)
end

module VSet = struct
  module VMap = Map.Make(Value)
  type t =
    | VSLeaf of runnable
    | VSNode of t VMap.t
  let find varray vs =
    let rec go i = function
      | VSLeaf p -> p
      | VSNode vs -> go (i+1) (VMap.find varray.(i) vs)
    in
      go 0 vs

  let find_match h varray vs =
    let min a b = match a,b with
      | (Some (ap, ah), Some (bp, bh)) -> if ah < bh then a else b
      | (None, x) | (x, None) -> x
    in
    let rec go i = function
      | VSLeaf p -> Some (p, h (p, varray))
      | VSNode vs -> begin match varray.(i) with
    | VDontCare -> VMap.fold (fun _ v -> min (go (i+1) v)) vs None
    | x ->
        try go (i+1) (VMap.find x vs)
        with Not_found -> None
  end
    in
      match go 0 vs with
  | Some (p, _) -> Some (p, varray)
  | None -> None

  let iter f vs =
    let rec go vlist = function
      | VSLeaf p -> f (p, Array.of_list (List.rev vlist))
      | VSNode vs ->
    VMap.iter (fun k v -> go (k::vlist) v) vs
    in
      go [] vs

  let seen varray vs =
    try (ignore (find varray vs); true)
    with Not_found -> false

  let empty = VSNode VMap.empty
  let add vector vs =
    let varray = snd vector in
    let len = Array.length varray in
    let rec makebranch i =
      if i = len then VSLeaf (fst vector)
      else VSNode (VMap.add varray.(i) (makebranch (i+1)) VMap.empty)
    in
    let rec go i = function
      | VSLeaf _ -> raise Not_found
      | VSNode vs ->
    try
      VSNode (VMap.add varray.(i) (go (i+1) (VMap.find varray.(i) vs)) vs)
    with Not_found ->
      VSNode (VMap.add varray.(i) (makebranch (i+1)) vs)
    in
      try go 0 vs
      with Not_found -> vs
  let singleton vector = add vector empty

  let filter p vs =
    let vs_filtered = ref empty in
    let f prog =
      if p prog then vs_filtered := add prog (!vs_filtered)
    in
      iter f vs;
      !vs_filtered
end

module VArray = struct
  type t = value array
  let compare = Pervasives.compare
end

module VArrayMap = Map.Make(VArray)
module VArraySet = Set.Make(VArray)

let partition_map p map =
  let f key value (pos, neg) =
    if p key then (value::pos, neg)
    else (pos, VArrayMap.add key value neg)
  in
    VArrayMap.fold f map ([], VArrayMap.empty)

let filter_map p map =
  let f key value pos =
    if p key then value::pos
    else pos
  in
    VArrayMap.fold f map []

let matches ?typeonly:(typeonly=false) x y =
  x = y || y = VDontCare || x = VDontCare || (typeonly && (typeof x == typeof y))

let varray_matches ?typeonly:(typeonly=false) have want =
  List.for_all2 (matches ~typeonly:typeonly) (Array.to_list have) (Array.to_list want)

let varray_meet have want =
  let f h w = if h = w then h else VDontCare in
    Array.of_list (List.map2 f (Array.to_list have) (Array.to_list want))

(** [partial_match_varray h w] holds when there exists some index i such that
    h.(i) = w.(i), and h.(i) is not VError, or a Boolean.  The non-Boolean
    condition prevents us from expanding goals for Booleans.  *)
let partial_match_varray have want =
  let strict_match x = function
    | VError | VBool _ -> false
    | y -> x = y
  in
    List.exists2 strict_match (Array.to_list have) (Array.to_list want)

(** Compute the residual goal that results from the partial fulfilment of
    [want] by [have]. *)
let residual_goal have want =
  let f h w =
    if matches h w then VDontCare else w
  in
    Array.of_list (List.map2 f (Array.to_list have) (Array.to_list want))

let type_of_varray varray =
  let defined x = x != VError && x != VDontCare in
    try begin match List.find defined (Array.to_list varray) with
      | VInt _ -> TInt
      | VBool _ -> TBool
      | _ -> failwith "impossible"
    end with Not_found -> failwith "No type for varray!"

(** Compute the downwards closure of a list of values (w.r.t. the product
    ordering, where the order on values is the lifted flat ordering, with
    VDontCare as bottom) *)
let rec down = function
  | [] -> [[]]
  | (VDontCare::xs) -> List.map (fun x -> VDontCare::x) (down xs)
  | (x::xs) -> let ds = down xs in
      List.map (fun xs -> VDontCare::xs) ds
      @ List.map (fun xs -> x::xs) ds
