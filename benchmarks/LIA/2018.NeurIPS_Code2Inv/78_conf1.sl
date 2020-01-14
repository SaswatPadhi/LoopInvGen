(set-logic LIA)

(synth-inv inv-f ((i Int) (conf_0 Int) (x Int) (y Int) (tmp Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (i_4 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (y_0 Int)))

(define-fun pre-f ((i Int) (conf_0 Int) (x Int) (y Int) (tmp Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (i_4 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (y_0 Int)) Bool
    (and (= i i_1) (= conf_0 conf_0_0) (= x x_0) (= y y_0) (= conf_0_0 2) (= i_1 0) (>= x_0 0) (>= y_0 0) (>= x_0 y_0)))
(define-fun trans-f ((i Int) (conf_0 Int) (x Int) (y Int) (tmp Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (i_4 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (y_0 Int) (i! Int) (conf_0! Int) (x! Int) (y! Int) (tmp! Int) (i_0! Int) (i_1! Int) (i_2! Int) (i_3! Int) (i_4! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (x_0! Int) (y_0! Int)) Bool
    (or (and (= i_2 i) (= conf_0_1 conf_0) (= i_2 i!) (= conf_0_1 conf_0!) (= i i!) (= conf_0 conf_0!) (= x x!) (= y y!) (= tmp tmp!)) (and (= i_2 i) (= conf_0_1 conf_0) (< i_2 y_0) (= i_3 (+ i_2 1)) (= conf_0_2 (- 161 conf_0_1)) (= i_4 i_3) (= conf_0_3 conf_0_2) (= i_4 i!) (= conf_0_3 conf_0!) (= x x_0) (= x! x_0) (= y y_0) (= y! y_0) (= tmp tmp!)) (and (= i_2 i) (= conf_0_1 conf_0) (not (< i_2 y_0)) (= i_4 i_2) (= conf_0_3 conf_0_1) (= i_4 i!) (= conf_0_3 conf_0!) (= x x_0) (= x! x_0) (= y y_0) (= y! y_0) (= tmp tmp!))))
(define-fun post-f ((i Int) (conf_0 Int) (x Int) (y Int) (tmp Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (i_4 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (x_0 Int) (y_0 Int)) Bool
    (or (not (and (= i i_2) (= conf_0 conf_0_1) (= x x_0) (= y y_0))) (not (and (< i_2 y_0) (not (<= 0 i_2))))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

