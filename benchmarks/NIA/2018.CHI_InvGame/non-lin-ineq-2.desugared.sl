(set-logic NIA)

(synth-inv inv-f ((i Int) (j Int) (k Int)))

(define-fun pre-f ((i Int) (j Int) (k Int)) Bool
    (and (= i 0) (> j 0) (> k 0)))
(define-fun trans-f ((i Int) (j Int) (k Int) (i! Int) (j! Int) (k! Int)) Bool
    (and (< i (* j k)) (= i! (+ i 1)) (= j! j) (= k! k)))
(define-fun post-f ((i Int) (j Int) (k Int)) Bool
    (or (< i (* j k)) (= i (* j k))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

