(set-logic NIA)

(synth-inv inv-f ((i Int) (j Int) (k Int)))

(define-fun pre-f ((i Int) (j Int) (k Int)) Bool
    (and (= i 0) (<= (* i j) k)))
(define-fun trans-f ((i Int) (j Int) (k Int) (i! Int) (j! Int) (k! Int)) Bool
    (and (< j 1000) (= i! (+ i 1)) (= j! j) (= k! (+ k j))))
(define-fun post-f ((i Int) (j Int) (k Int)) Bool
    (or (< j 1000) (<= (* i j) k)))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

