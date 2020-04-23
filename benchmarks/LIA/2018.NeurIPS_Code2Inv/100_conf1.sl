(set-logic LIA)

(synth-inv inv-f ((conf_0 Int) (n Int) (x Int) (y Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)))

(define-fun pre-f ((conf_0 Int) (n Int) (x Int) (y Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool
    (and (= conf_0 conf_0_0) (= n n_0) (= x x_1) (= y y_1) (= conf_0_0 3) (>= n_0 0) (= x_1 n_0) (= y_1 0)))
(define-fun trans-f ((conf_0 Int) (n Int) (x Int) (y Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int) (conf_0! Int) (n! Int) (x! Int) (y! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (n_0! Int) (x_0! Int) (x_1! Int) (x_2! Int) (x_3! Int) (y_0! Int) (y_1! Int) (y_2! Int) (y_3! Int)) Bool
    (or (and (= conf_0_1 conf_0) (= x_2 x) (= y_2 y) (= conf_0_1 conf_0!) (= x_2 x!) (= y_2 y!) (= conf_0 conf_0!) (= n n!) (= y y!)) (and (= conf_0_1 conf_0) (= x_2 x) (= y_2 y) (> x_2 0) (= y_3 (+ y_2 1)) (= conf_0_2 conf_0_1) (= x_3 (- x_2 1)) (= conf_0_3 778) (= conf_0_3 conf_0!) (= x_3 x!) (= y_3 y!) (= n n_0) (= n! n_0))))
(define-fun post-f ((conf_0 Int) (n Int) (x Int) (y Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool
    (or (not (and (= conf_0 conf_0_1) (= n n_0) (= x x_2) (= y y_2))) (not (and (not (> x_2 0)) (not (= y_2 n_0))))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

