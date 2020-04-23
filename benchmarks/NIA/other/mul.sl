(set-logic NIA)

(synth-inv inv-f ((i Int) (s Int) (j Int) (j0 Int)))

(define-fun pre-f ((i Int) (s Int) (j Int) (j0 Int)) Bool
    (and (= s 0) (= j j0) (>= j0 0)))
(define-fun trans-f ((i Int) (s Int) (j Int) (j0 Int) (i! Int) (s! Int) (j! Int) (j0! Int)) Bool
    (and (not (= 0 j)) (= s! (+ s i)) (= j! (- j 1)) (= i! i) (= j0! j0)))
(define-fun post-f ((i Int) (s Int) (j Int) (j0 Int)) Bool
    (or (not (= 0 j)) (= s (* i j0))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

