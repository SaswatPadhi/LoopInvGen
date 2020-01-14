(set-logic LIA)

(synth-inv inv-f ((c Int) (conf_0 Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (c_5 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int)))

(define-fun pre-f ((c Int) (conf_0 Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (c_5 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int)) Bool
    (and (= c c_1) (= conf_0 conf_0_0) (= conf_0_0 4) (= c_1 0)))
(define-fun trans-f ((c Int) (conf_0 Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (c_5 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (c! Int) (conf_0! Int) (tmp! Int) (c_0! Int) (c_1! Int) (c_2! Int) (c_3! Int) (c_4! Int) (c_5! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (conf_0_4! Int)) Bool
    (or (and (= c_2 c) (= conf_0_1 conf_0) (= c_2 c!) (= conf_0_1 conf_0!) (= c c!) (= conf_0 conf_0!) (= tmp tmp!)) (and (= c_2 c) (= conf_0_1 conf_0) (not (= c_2 40)) (= c_3 (+ c_2 1)) (= conf_0_2 (- 763 778)) (= c_4 c_3) (= conf_0_3 conf_0_2) (= c_4 c!) (= conf_0_3 conf_0!) (= tmp tmp!)) (and (= c_2 c) (= conf_0_1 conf_0) (not (not (= c_2 40))) (= c_4 c_2) (= conf_0_3 conf_0_1) (= c_4 c!) (= conf_0_3 conf_0!) (= tmp tmp!)) (and (= c_2 c) (= conf_0_1 conf_0) (= c_2 40) (= c_5 1) (= conf_0_4 (- 594 147)) (= c_4 c_5) (= conf_0_3 conf_0_4) (= c_4 c!) (= conf_0_3 conf_0!) (= tmp tmp!)) (and (= c_2 c) (= conf_0_1 conf_0) (not (= c_2 40)) (= c_4 c_2) (= conf_0_3 conf_0_1) (= c_4 c!) (= conf_0_3 conf_0!) (= tmp tmp!))))
(define-fun post-f ((c Int) (conf_0 Int) (tmp Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (c_5 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int)) Bool
    (or (not (and (= c c_2) (= conf_0 conf_0_1))) (not (and (< c_2 0) (> c_2 40) (not (= c_2 40))))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

