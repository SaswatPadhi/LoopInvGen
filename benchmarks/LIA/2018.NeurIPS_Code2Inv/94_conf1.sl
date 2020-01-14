(set-logic LIA)

(synth-inv inv-f ((i Int) (j Int) (conf_0 Int) (k Int) (n Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (k_0 Int) (n_0 Int)))

(define-fun pre-f ((i Int) (j Int) (conf_0 Int) (k Int) (n Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (k_0 Int) (n_0 Int)) Bool
    (and (= i i_1) (= j j_1) (= conf_0 conf_0_0) (= k k_0) (= n n_0) (= conf_0_0 9) (>= k_0 0) (>= n_0 0) (= i_1 0) (= j_1 0)))
(define-fun trans-f ((i Int) (j Int) (conf_0 Int) (k Int) (n Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (k_0 Int) (n_0 Int) (i! Int) (j! Int) (conf_0! Int) (k! Int) (n! Int) (i_0! Int) (i_1! Int) (i_2! Int) (i_3! Int) (j_0! Int) (j_1! Int) (j_2! Int) (j_3! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (k_0! Int) (n_0! Int)) Bool
    (or (and (= i_2 i) (= j_2 j) (= conf_0_1 conf_0) (= i_2 i!) (= j_2 j!) (= conf_0_1 conf_0!) (= n n_0) (= n! n_0) (= j j!) (= conf_0 conf_0!) (= k k!)) (and (= i_2 i) (= j_2 j) (= conf_0_1 conf_0) (<= i_2 n_0) (= i_3 (+ i_2 1)) (= conf_0_2 153) (= j_3 (+ j_2 i_3)) (= conf_0_3 (+ 205 conf_0_2)) (= i_3 i!) (= j_3 j!) (= conf_0_3 conf_0!) (= k k_0) (= k! k_0) (= n n_0) (= n! n_0))))
(define-fun post-f ((i Int) (j Int) (conf_0 Int) (k Int) (n Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (k_0 Int) (n_0 Int)) Bool
    (or (not (and (= i i_2) (= j j_2) (= conf_0 conf_0_1) (= k k_0) (= n n_0))) (not (and (not (<= i_2 n_0)) (not (> (+ i_2 (+ j_2 k_0)) (* 2 n_0)))))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

