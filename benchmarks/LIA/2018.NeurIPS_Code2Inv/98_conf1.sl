(set-logic LIA)

(synth-inv inv-f ((i Int) (j Int) (conf_0 Int) (x Int) (y Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (y_0 Int) (y_1 Int)))

(define-fun pre-f ((i Int) (j Int) (conf_0 Int) (x Int) (y Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (y_0 Int) (y_1 Int)) Bool
    (and (= i i_1) (= j j_1) (= conf_0 conf_0_0) (= y y_1) (= conf_0_0 0) (= j_1 0) (= i_1 0) (= y_1 2)))
(define-fun trans-f ((i Int) (j Int) (conf_0 Int) (x Int) (y Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (y_0 Int) (y_1 Int) (i! Int) (j! Int) (conf_0! Int) (x! Int) (y! Int) (i_0! Int) (i_1! Int) (i_2! Int) (i_3! Int) (j_0! Int) (j_1! Int) (j_2! Int) (j_3! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (x_0! Int) (y_0! Int) (y_1! Int)) Bool
    (or (and (= i_2 i) (= j_2 j) (= conf_0_1 conf_0) (= i_2 i!) (= j_2 j!) (= conf_0_1 conf_0!) (= x x_0) (= x! x_0) (= j j!) (= conf_0 conf_0!) (= y y!)) (and (= i_2 i) (= j_2 j) (= conf_0_1 conf_0) (<= i_2 x_0) (= i_3 (+ i_2 1)) (= conf_0_2 conf_0_1) (= j_3 (+ j_2 y_1)) (= conf_0_3 conf_0_2) (= i_3 i!) (= j_3 j!) (= conf_0_3 conf_0!) (= x x_0) (= x! x_0) (= y y_1) (= y! y_1))))
(define-fun post-f ((i Int) (j Int) (conf_0 Int) (x Int) (y Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (y_0 Int) (y_1 Int)) Bool
    (or (not (and (= i i_2) (= j j_2) (= conf_0 conf_0_1) (= x x_0) (= y y_1))) (not (and (not (<= i_2 x_0)) (not (= i_2 j_2)) (not (not (= y_1 1)))))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

