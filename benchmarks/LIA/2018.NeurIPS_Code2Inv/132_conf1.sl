(set-logic LIA)

(synth-inv inv-f ((c Int) (i Int) (j Int) (conf_0 Int) (t Int) (tmp Int) (c_0 Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (i_4 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (conf_0_5 Int) (t_0 Int) (t_1 Int) (t_2 Int) (t_3 Int)))

(define-fun pre-f ((c Int) (i Int) (j Int) (conf_0 Int) (t Int) (tmp Int) (c_0 Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (i_4 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (conf_0_5 Int) (t_0 Int) (t_1 Int) (t_2 Int) (t_3 Int)) Bool
    (and (= i i_1) (= conf_0 conf_0_0) (= conf_0_0 0) (= i_1 0)))
(define-fun trans-f ((c Int) (i Int) (j Int) (conf_0 Int) (t Int) (tmp Int) (c_0 Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (i_4 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (conf_0_5 Int) (t_0 Int) (t_1 Int) (t_2 Int) (t_3 Int) (c! Int) (i! Int) (j! Int) (conf_0! Int) (t! Int) (tmp! Int) (c_0! Int) (i_0! Int) (i_1! Int) (i_2! Int) (i_3! Int) (i_4! Int) (j_0! Int) (j_1! Int) (j_2! Int) (j_3! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (conf_0_4! Int) (conf_0_5! Int) (t_0! Int) (t_1! Int) (t_2! Int) (t_3! Int)) Bool
    (or (and (= i_2 i) (= j_1 j) (= conf_0_1 conf_0) (= t_1 t) (= i_2 i!) (= j_1 j!) (= conf_0_1 conf_0!) (= t_1 t!) (= c c!) (= i i!) (= j j!) (= conf_0 conf_0!) (= t t!) (= tmp tmp!)) (and (= i_2 i) (= j_1 j) (= conf_0_1 conf_0) (= t_1 t) (> c_0 48) (< c_0 57) (= j_2 (+ i_2 i_2)) (= conf_0_2 (+ 239 8)) (= t_2 (- c_0 48)) (= conf_0_3 conf_0_2) (= i_3 (+ j_2 t_2)) (= conf_0_4 (- conf_0_3 conf_0_3)) (= i_4 i_3) (= j_3 j_2) (= conf_0_5 conf_0_4) (= t_3 t_2) (= i_4 i!) (= j_3 j!) (= conf_0_5 conf_0!) (= t_3 t!) (= c c_0) (= c! c_0) (= tmp tmp!)) (and (= i_2 i) (= j_1 j) (= conf_0_1 conf_0) (= t_1 t) (> c_0 48) (not (< c_0 57)) (= i_4 i_2) (= j_3 j_1) (= conf_0_5 conf_0_1) (= t_3 t_1) (= i_4 i!) (= j_3 j!) (= conf_0_5 conf_0!) (= t_3 t!) (= c c_0) (= c! c_0) (= tmp tmp!)) (and (= i_2 i) (= j_1 j) (= conf_0_1 conf_0) (= t_1 t) (not (> c_0 48)) (= i_4 i_2) (= j_3 j_1) (= conf_0_5 conf_0_1) (= t_3 t_1) (= i_4 i!) (= j_3 j!) (= conf_0_5 conf_0!) (= t_3 t!) (= c c_0) (= c! c_0) (= tmp tmp!))))
(define-fun post-f ((c Int) (i Int) (j Int) (conf_0 Int) (t Int) (tmp Int) (c_0 Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (i_4 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (conf_0_5 Int) (t_0 Int) (t_1 Int) (t_2 Int) (t_3 Int)) Bool
    (or (not (and (= c c_0) (= i i_2) (= j j_1) (= conf_0 conf_0_1) (= t t_1))) (not (and (not (>= i_2 0))))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

