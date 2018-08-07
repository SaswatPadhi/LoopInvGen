open Base
open LoopInvGen

let prune_with_neg_example_1 () =
  Alcotest.check_raises "no more literals" Exceptions.NoSuchFunction (
    fun () -> let f = Hashtbl.Poly.of_alist_exn
              in ignore (BFL.pruneWithNegativeExamples
                          []
                          (List.map ~f [ [(1, false) ; (2, false)]
                                       ; [(2, true)]
                                       ])))

let prune_with_neg_example_2 () =
  let f = Hashtbl.Poly.of_alist_exn in
  let res = BFL.pruneWithNegativeExamples
              [1; 2; 3]
              (List.map ~f [ [(1, false)] ])
  in Alcotest.(check (slist int compare)) "equivalent list" [1] res

let prune_with_neg_example_3 () =
  let f = Hashtbl.Poly.of_alist_exn in
  let res = BFL.pruneWithNegativeExamples
              [1; 2; 3; 4; 5]
              (List.map ~f [
                 [(1, true) ; (5, false) ; (3, true)] ;
                 [(2, false) ; (3, false)] ;
                 [(1, false) ; (4, false) ; (5, true)]
              ])
  in Alcotest.(check (slist int compare)) "equivalent list" [1; 2; 5] res

let learnCNF_xor_k2 () =
  let res = BFL.learnCNF [[false ; true] ; [true ; false]]
                         [[true ; true] ; [false ; false]]
                         ~n:2 ~conf:{ BFL.default_config with
                                        k = 2 ; auto_incr_k = false ; }
  in Alcotest.(check string) "identical"
                             "(and (or (not 1) (not 2)) (or 1 2))"
                             (CNF.to_string res ~stringify:Int.to_string)

let learnCNF_xor_k1 () =
  Alcotest.check_raises "not expressive enough" Exceptions.NoSuchFunction (
    fun () -> ignore (
                BFL.learnCNF [[false ; true] ; [true ; false]]
                             [[true ; true] ; [false ; false]]
                             ~n:2 ~conf:{ BFL.default_config with
                                          k = 1
                                        ; auto_incr_k = false
                                        }))

let all = [
  "Negative Pruning 1", `Quick, prune_with_neg_example_1 ;
  "Negative Pruning 2", `Quick, prune_with_neg_example_2 ;
  "Negative Pruning 3", `Quick, prune_with_neg_example_3 ;

  "No XOR in 1-CNF",    `Quick, learnCNF_xor_k1 ;
  "2-CNF learning XOR", `Quick, learnCNF_xor_k2 ;
]