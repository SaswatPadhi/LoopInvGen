(set-logic LIA)

(synth-inv inv-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (x Int) (y Int) (tmp Int) (conf_0_0 Int) (conf_1_0 Int) (conf_1_1 Int) (conf_1_2 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_3_0 Int) (conf_4_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int)))

(define-fun pre-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (x Int) (y Int) (tmp Int) (conf_0_0 Int) (conf_1_0 Int) (conf_1_1 Int) (conf_1_2 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_3_0 Int) (conf_4_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int)) Bool
    (and (= conf_0 conf_0_0) (= conf_1 conf_1_0) (= conf_2 conf_2_0) (= conf_3 conf_3_0) (= conf_4 conf_4_0) (= x x_0) (= y y_0) (= conf_0_0 6) (= conf_1_0 3) (= conf_2_0 4) (= conf_3_0 8) (= conf_4_0 3) (>= x_0 0) (<= x_0 2) (<= y_0 2) (>= y_0 0)))
(define-fun trans-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (x Int) (y Int) (tmp Int) (conf_0_0 Int) (conf_1_0 Int) (conf_1_1 Int) (conf_1_2 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_3_0 Int) (conf_4_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int) (conf_0! Int) (conf_1! Int) (conf_2! Int) (conf_3! Int) (conf_4! Int) (x! Int) (y! Int) (tmp! Int) (conf_0_0! Int) (conf_1_0! Int) (conf_1_1! Int) (conf_1_2! Int) (conf_2_0! Int) (conf_2_1! Int) (conf_2_2! Int) (conf_3_0! Int) (conf_4_0! Int) (x_0! Int) (x_1! Int) (x_2! Int) (y_0! Int) (y_1! Int) (y_2! Int)) Bool
    (or (and (= conf_1_1 conf_1) (= conf_2_1 conf_2) (= x_1 x) (= y_1 y) (= conf_1_1 conf_1!) (= conf_2_1 conf_2!) (= x_1 x!) (= y_1 y!) (= conf_0 conf_0!) (= conf_1 conf_1!) (= conf_2 conf_2!) (= conf_3 conf_3!) (= conf_4 conf_4!) (= x x!) (= y y!) (= tmp tmp!)) (and (= conf_1_1 conf_1) (= conf_2_1 conf_2) (= x_1 x) (= y_1 y) (= x_2 (+ x_1 2)) (= conf_2_2 (- 520 69)) (= y_2 (+ y_1 2)) (= conf_1_2 (- conf_0_0 conf_2_2)) (= conf_1_2 conf_1!) (= conf_2_2 conf_2!) (= x_2 x!) (= y_2 y!) (= conf_0 conf_0_0) (= conf_0! conf_0_0) (= conf_3 conf_3_0) (= conf_3! conf_3_0) (= conf_4 conf_4_0) (= conf_4! conf_4_0) (= tmp tmp!))))
(define-fun post-f ((conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (x Int) (y Int) (tmp Int) (conf_0_0 Int) (conf_1_0 Int) (conf_1_1 Int) (conf_1_2 Int) (conf_2_0 Int) (conf_2_1 Int) (conf_2_2 Int) (conf_3_0 Int) (conf_4_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (y_0 Int) (y_1 Int) (y_2 Int)) Bool
    (or (not (and (= conf_0 conf_0_0) (= conf_1 conf_1_1) (= conf_2 conf_2_1) (= conf_3 conf_3_0) (= conf_4 conf_4_0) (= x x_1) (= y y_1))) (not (and (= y_1 0) (not (not (= x_1 4)))))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

