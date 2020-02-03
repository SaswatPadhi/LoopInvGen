open Core
open Sexp

open LoopInvGen
open NormalForm
open Utils
open Sexp

let check_same expected result =
  Alcotest.(check string) "same" (normalize_spaces expected) (normalize_spaces result)

let nnf_of_atoms () =
  let s1 = "true" and s2 = "(not false)" in
  let e1 = s1 and e2 = s2 in
  let r1 = to_nnf (force_parse s1)
  and r2 = to_nnf (force_parse s2)
   in check_same e1 (to_string_hum r1)
    ; check_same e2 (to_string_hum r2)

let nnf_of_int_operators () =
  let s1 = "(+ 2 x)" and s2 = "(not (= x (+ 2 y)))" in
  let e1 = s1 and e2 = s2 in
  let r1 = to_nnf (force_parse s1)
  and r2 = to_nnf (force_parse s2)
   in check_same e1 (to_string_hum r1)
    ; check_same e2 (to_string_hum r2)

let nnf_of_binary_bool_operators () =
  let s = "(not (and (= x y) (or (= y z) (> y z))))" in
  let e = "(or (not (= x y)) (and (not (= y z)) (not (> y z))))" in
  let r = to_nnf (force_parse s)
   in check_same e (to_string_hum r)

let nnf_of_n_ary_bool_operators () =
  let s = "(not (and (= x y)
                     (or (= y z) (> y z))
                     (or p1 (not p2)
                         (and (not p3) p5
                              (or (not p2) p1 (not p4))))))" in
  let e = "(or (not (= x y))
               (and (not (= y z)) (not (> y z)))
               (and (not p1) p2
                    (or p3 (not p5)
                        (and p2 (not p1) p4))))" in
  let r = to_nnf (force_parse s)
   in check_same e (to_string_hum r)

let dnf_of_atoms () =
  let s1 = "true" and s2 = "(not false)" in
  let e1 = s1 and e2 = s2 in
  let r1 = to_dnf (force_parse s1)
  and r2 = to_dnf (force_parse s2)
   in check_same e1 (to_string_hum r1)
    ; check_same e2 (to_string_hum r2)

let dnf_of_int_operators () =
  let s1 = "(+ 2 x)" and s2 = "(not (= x (+ 2 y)))" in
  let e1 = s1 and e2 = s2 in
  let r1 = to_dnf (force_parse s1)
  and r2 = to_dnf (force_parse s2)
   in check_same e1 (to_string_hum r1)
    ; check_same e2 (to_string_hum r2)

let dnf_of_binary_bool_operators () =
  let s = "(not (or (= x y) (and (= y z) (or (and p1 p2) (> y z)))))" in
  let e = "(or (and (not (= y z)) (not (= x y)))
               (and (not p1) (not (> y z)) (not (= x y)))
               (and (not p2) (not (> y z)) (not (= x y))))" in
  let r = to_dnf (force_parse s)
   in check_same e (to_string_hum r)

let dnf_of_n_ary_bool_operators () =
  let s = "(not (and (= x y)
                     (or (= y z) (> y z))
                     (or p1 (not p2)
                         (and (not p3) p5
                              (or (not p2) p1 (not p4))))))" in
  let e = "(or (not (= x y))
               (and (not (= y z)) (not (> y z)))
               (and p3 (not p1) p2)
               (and (not p5) (not p1) p2)
               (and p2 (not p1) p4 (not p1) p2))" in
  let r = to_dnf (force_parse s)
   in check_same e (to_string_hum r)

let all = [
  "NNF of Atoms",                     `Quick, nnf_of_atoms ;
  "NNF of Integer operators",         `Quick, nnf_of_int_operators ;
  "NNF of Binary Boolean operators",  `Quick, nnf_of_binary_bool_operators ;
  "NNF of n-ary Boolean operators",   `Quick, nnf_of_n_ary_bool_operators ;
  "DNF of Atoms",                     `Quick, dnf_of_atoms ;
  "DNF of Integer operators",         `Quick, dnf_of_int_operators ;
  "DNF of Binary Boolean operators",  `Quick, dnf_of_binary_bool_operators ;
  "DNF of n-ary Boolean operators",   `Quick, dnf_of_n_ary_bool_operators ;
]