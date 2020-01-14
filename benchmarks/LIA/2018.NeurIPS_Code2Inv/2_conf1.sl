(set-logic LIA)

(synth-inv inv-f ((conf_0 Int) (x Int) (y Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)))

(define-fun pre-f ((conf_0 Int) (x Int) (y Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool
    (and (= conf_0 conf_0_0) (= x x_1) (= y y_1) (= conf_0_0 4) (= x_1 1) (= y_1 0)))
(define-fun trans-f ((conf_0 Int) (x Int) (y Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int) (conf_0! Int) (x! Int) (y! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (x_0! Int) (x_1! Int) (x_2! Int) (x_3! Int) (y_0! Int) (y_1! Int) (y_2! Int) (y_3! Int)) Bool
    (or (and (= conf_0_1 conf_0) (= x_2 x) (= y_2 y) (= conf_0_1 conf_0!) (= x_2 x!) (= y_2 y!) (= conf_0 conf_0!) (= x x!)) (and (= conf_0_1 conf_0) (= x_2 x) (= y_2 y) (< y_2 1000) (= x_3 (+ x_2 y_2)) (= conf_0_2 (- 469 conf_0_1)) (= y_3 (+ y_2 1)) (= conf_0_3 (+ 687 622)) (= conf_0_3 conf_0!) (= x_3 x!) (= y_3 y!))))
(define-fun post-f ((conf_0 Int) (x Int) (y Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool
    (or (not (and (= conf_0 conf_0_1) (= x x_2) (= y y_2))) (not (and (not (< y_2 1000)) (not (>= x_2 y_2))))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

