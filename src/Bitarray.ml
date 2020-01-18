(*
 * Bitarray implementation from JaneStreet
 * (https://raw.githubusercontent.com/janestreet/core_extended/4a1f08a72b6ab3846148a31b889904994ff77807/src/bitarray.ml)
 *
 * See:
 *  - https://discuss.ocaml.org/t/ann-v0-12-release-of-jane-street-packages/3499/7
 *  - https://github.com/janestreet/core_extended/issues/22
 *)

open Core

(* a single 63 bit chunk of the array, bounds checking is left to the main module.
   We can only use 62 bits, because of the sign bit *)
module Int63_chunk : sig
  type t

  val empty : t
  val get : t -> int -> bool
  val set : t -> int -> bool -> t
  val gen_incl : Int63.t -> Int63.t -> t Core_kernel.Quickcheck.Generator.t

end = struct
  open Int63

  type t = Int63.t

  let empty = zero

  let get t i = bit_and t (shift_left one i) > zero

  let set t i v =
    if v then bit_or t (shift_left one i)
    else bit_and t (bit_xor minus_one (shift_left one i))

  let gen_incl h l = Int63.gen_incl h l
end

type t = {
  data: Int63_chunk.t Array.t;
  length: int
}

(* We can't use the sign bit, so we only get to use 62 bits *)
let bits_per_bucket = 62

let create sz =
  if sz < 0 || sz > (Array.max_length * bits_per_bucket) then
    invalid_argf "invalid size" ();
  { data = Array.create ~len:(1 + (sz / bits_per_bucket)) Int63_chunk.empty;
    length = sz }
;;

let bucket i = i / bits_per_bucket
let index i = i mod bits_per_bucket
let bounds_check t i =
  if i < 0 || i >= t.length then
    invalid_argf "Bitarray: out of bounds" ();
;;

let get t i =
  bounds_check t i;
  Int63_chunk.get t.data.(bucket i) (index i)
;;

let set t i v =
  bounds_check t i;
  let bucket = bucket i in
  t.data.(bucket) <- Int63_chunk.set t.data.(bucket) (index i) v
;;

let clear t =
  Array.fill t.data ~pos:0 ~len:(Array.length t.data) Int63_chunk.empty
;;

(* Applies f to index 0, then index 1, ...*)
let fold =
  let rec loop t n ~init ~f =
    if n < t.length then
      loop t (n + 1) ~init:(f init (get t n)) ~f
    else
      init
  in
  fun t ~init ~f -> loop t 0 ~init ~f
;;

let fold2 =
  let rec loop t1 t2 n ~init ~f =
    if n < t1.length then
      loop t1 t2 (n + 1) ~init:(f init (get t1 n) (get t2 n)) ~f
    else
      init
  in
  fun t1 t2 ~init ~f -> loop t1 t2 0 ~init ~f
;;

let iter t ~f = fold t ~init:() ~f:(fun _ v -> f v)

let sexp_of_t t =
  Array.sexp_of_t Bool.sexp_of_t
    (Array.init t.length ~f:(fun i -> get t i))
;;

let t_of_sexp sexp =
  let a = Array.t_of_sexp Bool.t_of_sexp sexp in
  let t = create (Array.length a) in
  Array.iteri a ~f:(fun i v -> set t i v);
  t
;;

(* A bitarray created from the string "#b00011" will be represented by
   the bitarray with index 0 set to true, index 1 to true, index 2 to
   false, etc.*)
let of_string s =
  let prefix = String.prefix s 2 in
  let numeral = String.drop_prefix s 2 in
  let bvsize = String.length numeral in
  match prefix with
  | "#b" ->
     let bv = create bvsize in       
     let rec loop s bv i = if i >= 0
                           then match s with
                                | '0'::t -> set bv i false; loop t bv (i - 1)
                                | '1'::t -> set bv i true; loop t bv (i - 1)
                           else
                             bv in
     loop (String.to_list numeral) bv (bvsize - 1)
  | "#x" ->
     let bv = create (bvsize * 4) in
     let n = (bvsize - 1) in
     let rec loop s bv i = if i <= n
                           then match s with
                                | '0'::t -> set bv (i * 4) false;
                                            set bv ((i * 4) + 1) false;
                                            set bv ((i * 4) + 2) false;
                                            set bv ((i * 4) + 3) false;
                                            loop t bv (i + 1)
                                | '1'::t -> set bv (i * 4) true;
                                            set bv ((i * 4) + 1) false;
                                            set bv ((i * 4) + 2) false;
                                            set bv ((i * 4) + 3) false;
                                            loop t bv (i + 1)
                                | '2'::t -> set bv (i * 4) false;
                                            set bv ((i * 4) + 1) true;
                                            set bv ((i * 4) + 2) false;
                                            set bv ((i * 4) + 3) false;
                                            loop t bv (i + 1)
                                | '3'::t -> set bv (i * 4) true;
                                            set bv ((i * 4) + 1) true;
                                            set bv ((i * 4) + 2) false;
                                            set bv ((i * 4) + 3) false;
                                            loop t bv (i + 1)
                                | '4'::t -> set bv (i * 4) false;
                                            set bv ((i * 4) + 1) false;
                                            set bv ((i * 4) + 2) true;
                                            set bv ((i * 4) + 3) false;
                                            loop t bv (i + 1)
                                | '5'::t -> set bv (i * 4) true;
                                            set bv ((i * 4) + 1) false;
                                            set bv ((i * 4) + 2) true;
                                            set bv ((i * 4) + 3) false;
                                            loop t bv (i + 1)
                                | '6'::t -> set bv (i * 4) false;
                                            set bv ((i * 4) + 1) true;
                                            set bv ((i * 4) + 2) true;
                                            set bv ((i * 4) + 3) false;
                                            loop t bv (i + 1)
                                | '7'::t -> set bv (i * 4) true;
                                            set bv ((i * 4) + 1) true;
                                            set bv ((i * 4) + 2) true;
                                            set bv ((i * 4) + 3) false;
                                            loop t bv (i + 1)
                                | '8'::t -> set bv (i * 4) false;
                                            set bv ((i * 4) + 1) false;
                                            set bv ((i * 4) + 2) false;
                                            set bv ((i * 4) + 3) true;
                                            loop t bv (i + 1)
                                | '9'::t -> set bv (i * 4) true;
                                            set bv ((i * 4) + 1) false;
                                            set bv ((i * 4) + 2) false;
                                            set bv ((i * 4) + 3) true;
                                            loop t bv (i + 1)
                                | 'a'::t -> set bv (i * 4) false;
                                            set bv ((i * 4) + 1) true;
                                            set bv ((i * 4) + 2) false;
                                            set bv ((i * 4) + 3) true;
                                            loop t bv (i + 1)
                                | 'b'::t -> set bv (i * 4) true;
                                            set bv ((i * 4) + 1) true;
                                            set bv ((i * 4) + 2) false;
                                            set bv ((i * 4) + 3) true;
                                            loop t bv (i + 1)
                                | 'c'::t -> set bv (i * 4) false;
                                            set bv ((i * 4) + 1) false;
                                            set bv ((i * 4) + 2) true;
                                            set bv ((i * 4) + 3) true;
                                            loop t bv (i + 1)
                                | 'd'::t -> set bv (i * 4) true;
                                            set bv ((i * 4) + 1) false;
                                            set bv ((i * 4) + 2) true;
                                            set bv ((i * 4) + 3) true;
                                            loop t bv (i + 1)
                                | 'e'::t -> set bv (i * 4) false;
                                            set bv ((i * 4) + 1) true;
                                            set bv ((i * 4) + 2) true;
                                            set bv ((i * 4) + 3) true;
                                            loop t bv (i + 1)
                                | 'f'::t -> set bv (i * 4) true;
                                            set bv ((i * 4) + 1) true;
                                            set bv ((i * 4) + 2) true;
                                            set bv ((i * 4) + 3) true;
                                            loop t bv (i + 1)
                           else
                             bv in
     loop (String.to_list (String.rev numeral)) bv 0
;;

(* TODO: If the length of the bitvector is a multiple of 4, represent with hex.*)
let to_string bv = "#b" ^ (fold bv ~init:"" ~f:(fun acc -> function
                               | false -> "0" ^ acc
                               | true -> "1" ^ acc))
;;

let rec add bv1 bv2 =
  let sum = create bv1.length in
  let s, _, _ = fold2 bv1 bv2 ~init:(sum, 0, 0) ~f:(fun (sum, carry, ind) v1 v2 ->
                    match v1, v2 with
                    | true, true -> if phys_equal carry 1
                                    then (set sum ind true; (sum, 1, ind + 1))
                                    else (set sum ind false; (sum, 1, ind + 1))
                    | false, true
                      | true, false -> if phys_equal carry 1
                                       then (set sum ind false; (sum, 1, ind + 1))
                                       else (set sum ind true; (sum, 0, ind + 1))
                    | false, false -> if phys_equal carry 1
                                      then (set sum ind true; (sum, 0, ind + 1))
                                      else (set sum ind false; (sum, 0, ind + 1))) in
  s
;;

let bvnot bv =
  let bv_new = create bv.length in
  fold bv ~init:(bv, 0) ~f:(fun (bv, i) v ->
      if phys_equal v true then (set bv_new i false; (bv, i + 1))
      else (set bv_new i true; (bv, i + 1)))
  ;
    bv_new
    
;;

let compare bv1 bv2 =
  let rec helper ind bv1 bv2 =
    if ind >= 0 then
      let v1 = get bv1 ind in
      let v2 = get bv2 ind in
      if phys_equal v1 v2 then helper (ind - 1) bv1 bv2
      else if phys_equal v1 false then -1 else 1
    else
      0
  in
  helper (bv1.length - 1) bv1 bv2
;;

let bvult bv1 bv2 =
  let c = compare bv1 bv2 in
  if c >= 0 then false else true
;;

let bvule bv1 bv2 =
  (bvult bv1 bv2) || ((compare bv1 bv2) = 0)
;;

let concat bv1 bv2 =
  let bv3 = create (bv1.length + bv2.length) in
  let bv1_, _ = fold bv1 ~init:(bv3, bv2.length) ~f:(fun (bv, i) v ->
                       set bv i v; (bv, i+1)) in
  let bv12, _ = fold bv2 ~init:(bv1_, 0) ~f:(fun (bv, i) v ->
                    set bv i v; (bv, i+1)) in
  bv12
;;

let bvuge bv1 bv2 =
  (bvult bv2 bv1) || ((compare bv1 bv2) = 0)
;;

let bvugt bv1 bv2 =
  bvult bv2 bv1
;;

let bvsub bv1 bv2 =
  let const_one = create bv2.length in
  set const_one 0 true;
  (add bv1 (add (bvnot bv2) const_one))
;;
