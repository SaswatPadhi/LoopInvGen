(set-logic LIA)

(synth-inv inv-f ((i Int) (j Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int)))

(define-fun pre-f ((i Int) (j Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int)) Bool
    (and (= i i_1) (= j j_1) (= i_1 1) (= j_1 10)))
(define-fun trans-f ((i Int) (j Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int) (i! Int) (j! Int) (i_0! Int) (i_1! Int) (i_2! Int) (i_3! Int) (j_0! Int) (j_1! Int) (j_2! Int) (j_3! Int)) Bool
    (or (and (= i_2 i) (= j_2 j) (= i_2 i!) (= j_2 j!)) (and (= i_2 i) (= j_2 j) (>= j_2 i_2) (= i_3 (+ i_2 2)) (= j_3 (- j_2 1)) (= i_3 i!) (= j_3 j!))))
(define-fun post-f ((i Int) (j Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (j_0 Int) (j_1 Int) (j_2 Int) (j_3 Int)) Bool
    (or (not (and (= i i_2) (= j j_2))) (not (and (not (>= j_2 i_2)) (not (= j_2 6))))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

