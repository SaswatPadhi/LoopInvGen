(set-logic LIA)

(synth-inv inv-f ((conf_0 Int) (lock Int) (x Int) (y Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (conf_0_5 Int) (conf_0_6 Int) (conf_0_7 Int) (lock_0 Int) (lock_1 Int) (lock_2 Int) (lock_3 Int) (lock_4 Int) (lock_5 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (x_4 Int) (x_5 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)))

(define-fun pre-f ((conf_0 Int) (lock Int) (x Int) (y Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (conf_0_5 Int) (conf_0_6 Int) (conf_0_7 Int) (lock_0 Int) (lock_1 Int) (lock_2 Int) (lock_3 Int) (lock_4 Int) (lock_5 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (x_4 Int) (x_5 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool
    (and (= conf_0 conf_0_0) (= lock lock_1) (= x x_1) (= y y_0) (= conf_0_0 5) (= x_1 y_0) (= lock_1 1)))
(define-fun trans-f ((conf_0 Int) (lock Int) (x Int) (y Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (conf_0_5 Int) (conf_0_6 Int) (conf_0_7 Int) (lock_0 Int) (lock_1 Int) (lock_2 Int) (lock_3 Int) (lock_4 Int) (lock_5 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (x_4 Int) (x_5 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int) (conf_0! Int) (lock! Int) (x! Int) (y! Int) (tmp! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (conf_0_4! Int) (conf_0_5! Int) (conf_0_6! Int) (conf_0_7! Int) (lock_0! Int) (lock_1! Int) (lock_2! Int) (lock_3! Int) (lock_4! Int) (lock_5! Int) (x_0! Int) (x_1! Int) (x_2! Int) (x_3! Int) (x_4! Int) (x_5! Int) (y_0! Int) (y_1! Int) (y_2! Int) (y_3! Int)) Bool
    (or (and (= conf_0_1 conf_0) (= lock_2 lock) (= x_2 x) (= y_1 y) (= conf_0_1 conf_0!) (= lock_2 lock!) (= x_2 x!) (= y_1 y!) (= conf_0 conf_0!) (= lock lock!) (= tmp tmp!)) (and (= conf_0_1 conf_0) (= lock_2 lock) (= x_2 x) (= y_1 y) (not (= x_2 y_1)) (= lock_3 1) (= conf_0_2 conf_0_1) (= x_3 y_1) (= conf_0_3 (+ 445 35)) (= conf_0_4 conf_0_3) (= lock_4 lock_3) (= x_4 x_3) (= y_2 y_1) (= conf_0_4 conf_0!) (= lock_4 lock!) (= x_4 x!) (= y_2 y!) (= tmp tmp!)) (and (= conf_0_1 conf_0) (= lock_2 lock) (= x_2 x) (= y_1 y) (not (= x_2 y_1)) (= lock_5 0) (= conf_0_5 (- conf_0_1 303)) (= x_5 y_1) (= conf_0_6 (- conf_0_5 403)) (= y_3 (+ y_1 1)) (= conf_0_7 73) (= conf_0_4 conf_0_7) (= lock_4 lock_5) (= x_4 x_5) (= y_2 y_3) (= conf_0_4 conf_0!) (= lock_4 lock!) (= x_4 x!) (= y_2 y!) (= tmp tmp!))))
(define-fun post-f ((conf_0 Int) (lock Int) (x Int) (y Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (conf_0_5 Int) (conf_0_6 Int) (conf_0_7 Int) (lock_0 Int) (lock_1 Int) (lock_2 Int) (lock_3 Int) (lock_4 Int) (lock_5 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (x_4 Int) (x_5 Int) (y_0 Int) (y_1 Int) (y_2 Int) (y_3 Int)) Bool
    (or (not (and (= conf_0 conf_0_1) (= lock lock_2) (= x x_2) (= y y_1))) (not (and (not (not (= x_2 y_1))) (not (= lock_2 1))))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

