(set-logic LIA)

(synth-inv inv-f ((conf_0 Int) (x Int) (y Int) (z Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int) (z_0 Int)))

(define-fun pre-f ((conf_0 Int) (x Int) (y Int) (z Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int) (z_0 Int)) Bool
    (and (= conf_0 conf_0_0) (= x x_1) (= conf_0_0 8) (= x_1 0)))
(define-fun trans-f ((conf_0 Int) (x Int) (y Int) (z Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int) (z_0 Int) (conf_0! Int) (x! Int) (y! Int) (z! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (conf_0_4! Int) (x_0! Int) (x_1! Int) (x_2! Int) (x_3! Int) (y_0! Int) (y_1! Int) (y_2! Int) (y_3! Int) (z_0! Int)) Bool
    (or (and (= conf_0_1 conf_0) (= x_2 x) (= y_1 y) (= conf_0_1 conf_0!) (= x_2 x!) (= y_1 y!) (= conf_0 conf_0!) (= y y!) (= z z!)) (and (= conf_0_1 conf_0) (= x_2 x) (= y_1 y) (< x_2 500) (= x_3 (+ x_2 1)) (= conf_0_2 conf_0_1) (<= z_0 y_1) (= y_2 z_0) (= conf_0_3 159) (= conf_0_4 conf_0_3) (= y_3 y_2) (= conf_0_4 conf_0!) (= x_3 x!) (= y_3 y!) (= z z_0) (= z! z_0)) (and (= conf_0_1 conf_0) (= x_2 x) (= y_1 y) (< x_2 500) (= x_3 (+ x_2 1)) (= conf_0_2 conf_0_1) (not (<= z_0 y_1)) (= conf_0_4 conf_0_2) (= y_3 y_1) (= conf_0_4 conf_0!) (= x_3 x!) (= y_3 y!) (= z z_0) (= z! z_0))))
(define-fun post-f ((conf_0 Int) (x Int) (y Int) (z Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int) (z_0 Int)) Bool
    (or (not (and (= conf_0 conf_0_1) (= x x_2) (= y y_1) (= z z_0))) (not (and (not (< x_2 500)) (not (>= z_0 y_1))))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

