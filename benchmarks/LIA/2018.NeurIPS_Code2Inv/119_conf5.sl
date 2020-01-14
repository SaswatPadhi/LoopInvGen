(set-logic LIA)

(synth-inv inv-f ((i Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (size Int) (sn Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_3_0 Int) (conf_4_0 Int) (conf_4_1 Int) (conf_4_2 Int) (size_0 Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int)))

(define-fun pre-f ((i Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (size Int) (sn Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_3_0 Int) (conf_4_0 Int) (conf_4_1 Int) (conf_4_2 Int) (size_0 Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int)) Bool
    (and (= i i_1) (= conf_0 conf_0_0) (= conf_1 conf_1_0) (= conf_2 conf_2_0) (= conf_3 conf_3_0) (= conf_4 conf_4_0) (= sn sn_1) (= conf_0_0 5) (= conf_1_0 2) (= conf_2_0 5) (= conf_3_0 8) (= conf_4_0 9) (= sn_1 0) (= i_1 1)))
(define-fun trans-f ((i Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (size Int) (sn Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_3_0 Int) (conf_4_0 Int) (conf_4_1 Int) (conf_4_2 Int) (size_0 Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int) (i! Int) (conf_0! Int) (conf_1! Int) (conf_2! Int) (conf_3! Int) (conf_4! Int) (size! Int) (sn! Int) (i_0! Int) (i_1! Int) (i_2! Int) (i_3! Int) (conf_0_0! Int) (conf_1_0! Int) (conf_2_0! Int) (conf_2_1! Int) (conf_2_2! Int) (conf_3_0! Int) (conf_4_0! Int) (conf_4_1! Int) (conf_4_2! Int) (size_0! Int) (sn_0! Int) (sn_1! Int) (sn_2! Int) (sn_3! Int)) Bool
    (or (and (= i_2 i) (= conf_2_1 conf_2) (= conf_4_1 conf_4) (= sn_2 sn) (= i_2 i!) (= conf_2_1 conf_2!) (= conf_4_1 conf_4!) (= sn_2 sn!) (= size size_0) (= size! size_0) (= conf_0 conf_0!) (= conf_1 conf_1!) (= conf_2 conf_2!) (= conf_3 conf_3!) (= conf_4 conf_4!) (= sn sn!)) (and (= i_2 i) (= conf_2_1 conf_2) (= conf_4_1 conf_4) (= sn_2 sn) (<= i_2 size_0) (= i_3 (+ i_2 1)) (= conf_2_2 (+ 617 709)) (= sn_3 (+ sn_2 1)) (= conf_4_2 (- 168 conf_2_2)) (= i_3 i!) (= conf_2_2 conf_2!) (= conf_4_2 conf_4!) (= sn_3 sn!) (= conf_0 conf_0_0) (= conf_0! conf_0_0) (= conf_1 conf_1_0) (= conf_1! conf_1_0) (= conf_3 conf_3_0) (= conf_3! conf_3_0) (= size size_0) (= size! size_0))))
(define-fun post-f ((i Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (size Int) (sn Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_3_0 Int) (conf_4_0 Int) (conf_4_1 Int) (conf_4_2 Int) (size_0 Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int)) Bool
    (or (not (and (= i i_2) (= conf_0 conf_0_0) (= conf_1 conf_1_0) (= conf_2 conf_2_1) (= conf_3 conf_3_0) (= conf_4 conf_4_1) (= size size_0) (= sn sn_2))) (not (and (not (<= i_2 size_0)) (not (= sn_2 0)) (not (= sn_2 size_0))))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

