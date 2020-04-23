(set-logic NIA)

(synth-inv inv-f ((i Int) (j Int) (k Int)))

(define-fun pre-f ((i Int) (j Int) (k Int)) Bool
    (and (= i 0) (= j 1) (= k 0)))
(define-fun trans-f ((i Int) (j Int) (k Int) (i! Int) (j! Int) (k! Int)) Bool
    (and (< i 1000) (= i! (+ i 1)) (= j! (+ j 1)) (= k! (+ k (* i! j!)))))
(define-fun post-f ((i Int) (j Int) (k Int)) Bool
    (or (< i 1000) (<= (* 1000 j) k)))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

