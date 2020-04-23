(set-logic NIA)

(synth-inv inv-f ((n Int) (sum Int) (i Int)))

(define-fun pre-f ((n Int) (sum Int) (i Int)) Bool
    (and (<= 1 n) (<= n 1000) (= sum 0) (= i 1)))
(define-fun trans-f ((n Int) (sum Int) (i Int) (n! Int) (sum! Int) (i! Int)) Bool
    (and (<= i n) (= i! (+ i 1)) (= sum! (+ sum i)) (= n! n)))
(define-fun post-f ((n Int) (sum Int) (i Int)) Bool
    (or (<= i n) (= (* sum 2) (* n (+ n 1)))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

