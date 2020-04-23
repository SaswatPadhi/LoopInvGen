(set-logic LIA)

(synth-inv inv-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (x Int) (y Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_4_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int)))

(define-fun pre-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (x Int) (y Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_4_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int)) Bool
    (and (= conf_0 conf_0_0) (= conf_1 conf_1_0) (= conf_2 conf_2_0) (= conf_3 conf_3_0) (= conf_4 conf_4_0) (= x x_1) (= conf_0_0 8) (= conf_1_0 7) (= conf_2_0 7) (= conf_3_0 7) (= conf_4_0 5) (= x_1 1)))
(define-fun trans-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (x Int) (y Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_4_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int) (conf_0! Int) (conf_1! Int) (conf_2! Int) (conf_3! Int) (conf_4! Int) (x! Int) (y! Int) (conf_0_0! Int) (conf_1_0! Int) (conf_2_0! Int) (conf_3_0! Int) (conf_3_1! Int) (conf_3_2! Int) (conf_4_0! Int) (x_0! Int) (x_1! Int) (x_2! Int) (x_3! Int) (y_0! Int)) Bool
    (or (and (= conf_3_1 conf_3) (= x_2 x) (= conf_3_1 conf_3!) (= x_2 x!) (= y y_0) (= y! y_0) (= conf_0 conf_0!) (= conf_1 conf_1!) (= conf_2 conf_2!) (= conf_3 conf_3!) (= conf_4 conf_4!)) (and (= conf_3_1 conf_3) (= x_2 x) (< x_2 y_0) (= x_3 (+ x_2 x_2)) (= conf_3_2 conf_3_1) (= conf_3_2 conf_3!) (= x_3 x!) (= conf_0 conf_0_0) (= conf_0! conf_0_0) (= conf_1 conf_1_0) (= conf_1! conf_1_0) (= conf_2 conf_2_0) (= conf_2! conf_2_0) (= conf_4 conf_4_0) (= conf_4! conf_4_0) (= y y_0) (= y! y_0))))
(define-fun post-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (x Int) (y Int) (conf_0_0 Int) (conf_1_0 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_3_1 Int) (conf_3_2 Int) (conf_4_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (y_0 Int)) Bool
    (or (not (and (= conf_0 conf_0_0) (= conf_1 conf_1_0) (= conf_2 conf_2_0) (= conf_3 conf_3_1) (= conf_4 conf_4_0) (= x x_2) (= y y_0))) (not (and (not (< x_2 y_0)) (not (>= x_2 1))))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

