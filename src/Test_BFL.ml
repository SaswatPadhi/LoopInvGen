open Core
open Exceptions
open Utils

let uniform_costs n =
  Hashtbl.Poly.of_alist_exn (
    List.range_map ~stop:`inclusive 1 n ~f:(fun i -> (i, 1.0)))

let prune_with_neg_example_1 () =
  Alcotest.check_raises "no more literals" NoSuchFunction (
    fun () -> let f = Hashtbl.Poly.of_alist_exn
              in ignore (BFL.pruneWithNegativeExamples
                          []
                          (uniform_costs 5)
                          (List.map ~f [
                              [(1, false) ; (2, false)] ;
                              [(2, true)]
                          ])))

let prune_with_neg_example_2 () =
  let f = Hashtbl.Poly.of_alist_exn in
  let res = BFL.pruneWithNegativeExamples
              [1; 2; 3]
              (uniform_costs 3)
              (List.map ~f [ [(1, false)] ])
  in Alcotest.(check (slist int compare)) "equivalent list" [1] res

let prune_with_neg_example_3 () =
  let f = Hashtbl.Poly.of_alist_exn in
  let res = BFL.pruneWithNegativeExamples
              [1; 2; 3; 4; 5]
              (uniform_costs 5)
              (List.map ~f [
                 [(1, true) ; (5, false) ; (3, true)] ;
                 [(2, false) ; (3, false)] ;
                 [(1, false) ; (4, false) ; (5, true)]
              ])
  in Alcotest.(check (slist int compare)) "equivalent list" [1; 2; 5] res

let learnKCNF_xor_k2 () =
  let res = BFL.learnKCNF ~k:2 ~n:2 [[false ; true] ; [true ; false]]
                                    [[true ; true] ; [false ; false]]
  in Alcotest.(check string) "identical"
                             "(and (or (not 1) (not 2)) (or 1 2))"
                             (CNF.to_string res ~stringify:string_of_int)

let learnKCNF_xor_k1 () =
  Alcotest.check_raises "not expressive enough" NoSuchFunction (
    fun () -> ignore (BFL.learnKCNF ~k:1 ~n:2
                                    [[false ; true] ; [true ; false]]
                                    [[true ; true] ; [false ; false]]))

let all = [
  "Negative Pruning 1", `Quick, prune_with_neg_example_1 ;
  "Negative Pruning 2", `Quick, prune_with_neg_example_2 ;
  "Negative Pruning 3", `Quick, prune_with_neg_example_3 ;

  "No XOR in 1-CNF",    `Quick, learnKCNF_xor_k1 ;
  "2-CNF learning XOR", `Quick, learnKCNF_xor_k2 ;
]