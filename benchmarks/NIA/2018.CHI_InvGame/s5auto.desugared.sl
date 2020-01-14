(set-logic NIA)

(synth-inv inv-f ((i Int) (j Int) (k Int)))

(define-fun pre-f ((i Int) (j Int) (k Int)) Bool
    (and (= j 0) (= i 0) (> k 0)))
(define-fun trans-f ((i Int) (j Int) (k Int) (i! Int) (j! Int) (k! Int)) Bool
    (and (< j k) (= k! k) (= j! (+ j 1)) (= i! (+ i (* 2 k)))))
(define-fun post-f ((i Int) (j Int) (k Int)) Bool
    (or (< j k) (= i (* 2 (* k j)))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

