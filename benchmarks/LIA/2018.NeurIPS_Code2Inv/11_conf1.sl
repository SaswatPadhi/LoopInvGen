(set-logic LIA)

(synth-inv inv-f ((conf_0 Int) (x Int) (y Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int)))

(define-fun pre-f ((conf_0 Int) (x Int) (y Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int)) Bool
    (and (= conf_0 conf_0_0) (= x x_0) (= y y_0) (= conf_0_0 3) (>= x_0 0) (<= x_0 10) (<= y_0 10) (>= y_0 0)))
(define-fun trans-f ((conf_0 Int) (x Int) (y Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int) (conf_0! Int) (x! Int) (y! Int) (tmp! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (x_0! Int) (x_1! Int) (x_2! Int) (y_0! Int) (y_1! Int) (y_2! Int)) Bool
    (or (and (= conf_0_1 conf_0) (= x_1 x) (= y_1 y) (= conf_0_1 conf_0!) (= x_1 x!) (= y_1 y!) (= conf_0 conf_0!) (= x x!) (= y y!) (= tmp tmp!)) (and (= conf_0_1 conf_0) (= x_1 x) (= y_1 y) (= x_2 (+ x_1 10)) (= conf_0_2 (+ conf_0_1 350)) (= y_2 (+ y_1 10)) (= conf_0_3 (- 398 257)) (= conf_0_3 conf_0!) (= x_2 x!) (= y_2 y!) (= tmp tmp!))))
(define-fun post-f ((conf_0 Int) (x Int) (y Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int)) Bool
    (or (not (and (= conf_0 conf_0_1) (= x x_1) (= y y_1))) (not (and (= x_1 20) (not (not (= y_1 0)))))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

