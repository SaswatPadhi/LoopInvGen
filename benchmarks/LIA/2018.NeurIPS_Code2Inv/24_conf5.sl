(set-logic LIA)

(synth-inv inv-f ((i Int) (j Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_4_0 Int) (conf_4_1 Int) (conf_4_2 Int)))

(define-fun pre-f ((i Int) (j Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_4_0 Int) (conf_4_1 Int) (conf_4_2 Int)) Bool
    (and (= i i_1) (= j j_1) (= conf_0 conf_0_0) (= conf_1 conf_1_0) (= conf_2 conf_2_0) (= conf_3 conf_3_0) (= conf_4 conf_4_0) (= conf_0_0 3) (= conf_1_0 0) (= conf_2_0 5) (= conf_3_0 3) (= conf_4_0 0) (= i_1 1) (= j_1 10)))
(define-fun trans-f ((i Int) (j Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_4_0 Int) (conf_4_1 Int) (conf_4_2 Int) (i! Int) (j! Int) (conf_0! Int) (conf_1! Int) (conf_2! Int) (conf_3! Int) (conf_4! Int) (i_0! Int) (i_1! Int) (i_2! Int) (i_3! Int) (j_0! Int) (j_1! Int) (j_2! Int) (j_3! Int) (conf_0_0! Int) (conf_1_0! Int) (conf_2_0! Int) (conf_3_0! Int) (conf_3_1! Int) (conf_3_2! Int) (conf_4_0! Int) (conf_4_1! Int) (conf_4_2! Int)) Bool
    (or (and (= i_2 i) (= j_2 j) (= conf_3_1 conf_3) (= conf_4_1 conf_4) (= i_2 i!) (= j_2 j!) (= conf_3_1 conf_3!) (= conf_4_1 conf_4!) (= conf_0 conf_0!) (= conf_1 conf_1!) (= conf_2 conf_2!) (= conf_3 conf_3!) (= conf_4 conf_4!)) (and (= i_2 i) (= j_2 j) (= conf_3_1 conf_3) (= conf_4_1 conf_4) (>= j_2 i_2) (= i_3 (+ i_2 2)) (= conf_4_2 conf_4_1) (= j_3 (- j_2 1)) (= conf_3_2 conf_0_0) (= i_3 i!) (= j_3 j!) (= conf_3_2 conf_3!) (= conf_4_2 conf_4!) (= conf_0 conf_0_0) (= conf_0! conf_0_0) (= conf_1 conf_1_0) (= conf_1! conf_1_0) (= conf_2 conf_2_0) (= conf_2! conf_2_0))))
(define-fun post-f ((i Int) (j Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_4_0 Int) (conf_4_1 Int) (conf_4_2 Int)) Bool
    (or (not (and (= i i_2) (= j j_2) (= conf_0 conf_0_0) (= conf_1 conf_1_0) (= conf_2 conf_2_0) (= conf_3 conf_3_1) (= conf_4 conf_4_1))) (not (and (not (>= j_2 i_2)) (not (= j_2 6))))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

