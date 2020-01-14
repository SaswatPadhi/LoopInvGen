(set-logic LIA)

(synth-inv inv-f ((conf_0 Int) (sn Int) (x Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)))

(define-fun pre-f ((conf_0 Int) (sn Int) (x Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)) Bool
    (and (= conf_0 conf_0_0) (= sn sn_1) (= x x_1) (= conf_0_0 7) (= sn_1 0) (= x_1 0)))
(define-fun trans-f ((conf_0 Int) (sn Int) (x Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (conf_0! Int) (sn! Int) (x! Int) (tmp! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (sn_0! Int) (sn_1! Int) (sn_2! Int) (sn_3! Int) (x_0! Int) (x_1! Int) (x_2! Int) (x_3! Int)) Bool
    (or (and (= conf_0_1 conf_0) (= sn_2 sn) (= x_2 x) (= conf_0_1 conf_0!) (= sn_2 sn!) (= x_2 x!) (= conf_0 conf_0!) (= sn sn!) (= x x!) (= tmp tmp!)) (and (= conf_0_1 conf_0) (= sn_2 sn) (= x_2 x) (= x_3 (+ x_2 1)) (= conf_0_2 conf_0_1) (= sn_3 (+ sn_2 1)) (= conf_0_3 (+ conf_0_2 conf_0_2)) (= conf_0_3 conf_0!) (= sn_3 sn!) (= x_3 x!) (= tmp tmp!))))
(define-fun post-f ((conf_0 Int) (sn Int) (x Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (sn_0 Int) (sn_1 Int) (sn_2 Int) (sn_3 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)) Bool
    (or (not (and (= conf_0 conf_0_1) (= sn sn_2) (= x x_2))) (not (and (not (= sn_2 (- 1))) (not (= sn_2 x_2))))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

