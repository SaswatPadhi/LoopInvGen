(set-logic LIA)

(synth-inv inv_fun ((i Int) (j Int)))

(define-fun pre_fun ((i Int) (j Int)) Bool
    (and (= i 1) (= j 10)))
(define-fun trans_fun ((i Int) (j Int) (i! Int) (j! Int)) Bool
    (and (>= j i) (= i! (+ i 2)) (= j! (+ j (- 0 1)))))
(define-fun post_fun ((i Int) (j Int)) Bool
    (or (>= j i) (= j 6)))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

