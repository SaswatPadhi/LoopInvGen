(set-logic NIA)

(synth-inv inv-f ((i Int) (k Int)))

(define-fun pre-f ((i Int) (k Int)) Bool
    (and (= i 0) (= k 0)))
(define-fun trans-f ((i Int) (k Int) (i! Int) (k! Int)) Bool
    (and (< i 1000) (= i! (+ i 1)) (= k! (+ k (* i! i!)))))
(define-fun post-f ((i Int) (k Int)) Bool
    (or (< i 1000) (<= 1000000 k)))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

