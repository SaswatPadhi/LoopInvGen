(set-logic LIA)

(synth-inv inv-f ((i Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (x Int) (y Int) (tmp Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (i_4 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_1_1 Int) (conf_1_2 Int) (conf_1_3 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_4_0 Int) (x_0 Int) (y_0 Int)))

(define-fun pre-f ((i Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (x Int) (y Int) (tmp Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (i_4 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_1_1 Int) (conf_1_2 Int) (conf_1_3 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_4_0 Int) (x_0 Int) (y_0 Int)) Bool
    (and (= i i_1) (= conf_0 conf_0_0) (= conf_1 conf_1_0) (= conf_2 conf_2_0) (= conf_3 conf_3_0) (= conf_4 conf_4_0) (= x x_0) (= y y_0) (= conf_0_0 1) (= conf_1_0 6) (= conf_2_0 5) (= conf_3_0 1) (= conf_4_0 2) (= i_1 0) (>= x_0 0) (>= y_0 0) (>= x_0 y_0)))
(define-fun trans-f ((i Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (x Int) (y Int) (tmp Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (i_4 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_1_1 Int) (conf_1_2 Int) (conf_1_3 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_4_0 Int) (x_0 Int) (y_0 Int) (i! Int) (conf_0! Int) (conf_1! Int) (conf_2! Int) (conf_3! Int) (conf_4! Int) (x! Int) (y! Int) (tmp! Int) (i_0! Int) (i_1! Int) (i_2! Int) (i_3! Int) (i_4! Int) (conf_0_0! Int) (conf_1_0! Int) (conf_1_1! Int) (conf_1_2! Int) (conf_1_3! Int) (conf_2_0! Int) (conf_3_0! Int) (conf_4_0! Int) (x_0! Int) (y_0! Int)) Bool
    (or (and (= i_2 i) (= conf_1_1 conf_1) (= i_2 i!) (= conf_1_1 conf_1!) (= i i!) (= conf_0 conf_0!) (= conf_1 conf_1!) (= conf_2 conf_2!) (= conf_3 conf_3!) (= conf_4 conf_4!) (= x x!) (= y y!) (= tmp tmp!)) (and (= i_2 i) (= conf_1_1 conf_1) (< i_2 y_0) (= i_3 (+ i_2 1)) (= conf_1_2 (- conf_2_0 conf_4_0)) (= i_4 i_3) (= conf_1_3 conf_1_2) (= i_4 i!) (= conf_1_3 conf_1!) (= conf_0 conf_0_0) (= conf_0! conf_0_0) (= conf_2 conf_2_0) (= conf_2! conf_2_0) (= conf_3 conf_3_0) (= conf_3! conf_3_0) (= conf_4 conf_4_0) (= conf_4! conf_4_0) (= x x_0) (= x! x_0) (= y y_0) (= y! y_0) (= tmp tmp!)) (and (= i_2 i) (= conf_1_1 conf_1) (not (< i_2 y_0)) (= i_4 i_2) (= conf_1_3 conf_1_1) (= i_4 i!) (= conf_1_3 conf_1!) (= conf_0 conf_0_0) (= conf_0! conf_0_0) (= conf_2 conf_2_0) (= conf_2! conf_2_0) (= conf_3 conf_3_0) (= conf_3! conf_3_0) (= conf_4 conf_4_0) (= conf_4! conf_4_0) (= x x_0) (= x! x_0) (= y y_0) (= y! y_0) (= tmp tmp!))))
(define-fun post-f ((i Int) (conf_0 Int) (conf_1 Int) (conf_2 Int) (conf_3 Int) (conf_4 Int) (x Int) (y Int) (tmp Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (i_4 Int) (conf_0_0 Int) (conf_1_0 Int) (conf_1_1 Int) (conf_1_2 Int) (conf_1_3 Int) (conf_2_0 Int) (conf_3_0 Int) (conf_4_0 Int) (x_0 Int) (y_0 Int)) Bool
    (or (not (and (= i i_2) (= conf_0 conf_0_0) (= conf_1 conf_1_1) (= conf_2 conf_2_0) (= conf_3 conf_3_0) (= conf_4 conf_4_0) (= x x_0) (= y y_0))) (not (and (< i_2 y_0) (not (<= 0 i_2))))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

