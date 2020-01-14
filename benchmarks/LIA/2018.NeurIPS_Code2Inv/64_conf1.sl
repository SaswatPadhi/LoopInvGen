(set-logic LIA)

(synth-inv inv-f ((conf_0 Int) (x Int) (y Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int)))

(define-fun pre-f ((conf_0 Int) (x Int) (y Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int)) Bool
    (and (= conf_0 conf_0_0) (= x x_1) (= conf_0_0 2) (= x_1 1)))
(define-fun trans-f ((conf_0 Int) (x Int) (y Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (conf_0! Int) (x! Int) (y! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (x_0! Int) (x_1! Int) (x_2! Int) (x_3! Int) (y_0! Int) (y_1! Int) (y_2! Int)) Bool
    (or (and (= conf_0_1 conf_0) (= x_2 x) (= y_1 y) (= conf_0_1 conf_0!) (= x_2 x!) (= y_1 y!) (= conf_0 conf_0!) (= y y!)) (and (= conf_0_1 conf_0) (= x_2 x) (= y_1 y) (<= x_2 10) (= y_2 (- 10 x_2)) (= conf_0_2 conf_0_1) (= x_3 (+ x_2 1)) (= conf_0_3 (+ 686 conf_0_2)) (= conf_0_3 conf_0!) (= x_3 x!) (= y_2 y!))))
(define-fun post-f ((conf_0 Int) (x Int) (y Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int)) Bool
    (or (not (and (= conf_0 conf_0_1) (= x x_2) (= y y_1))) (not (and (not (<= x_2 10)) (not (< y_1 10))))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

