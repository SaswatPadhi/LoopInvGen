(set-logic LIA)

(synth-inv inv_fun ((i Int) (j Int) (k Int) (c1 Int) (c2 Int) (n Int) (v Int)))

(define-fun pre_fun ((i Int) (j Int) (k Int) (c1 Int) (c2 Int) (n Int) (v Int)) Bool
    (and (> n 0) (< n 10) (= k 0) (= i 0) (= c1 4000) (= c2 2000)))
(define-fun trans_fun ((i Int) (j Int) (k Int) (c1 Int) (c2 Int) (n Int) (v Int) (i! Int) (j! Int) (k! Int) (c1! Int) (c2! Int) (n! Int) (v! Int)) Bool
    (or (and (>= i n) (= i! i) (= j! j) (= k! k) (= c1! c1) (= c2! c2) (= n! n) (= v! v)) (and (< i n) (= i! (+ i 1)) (= j! j) (= k! (+ k c1)) (= c1! c1) (= c2! c2) (= n! n) (= v! 0)) (and (< i n) (= i! (+ i 1)) (= j! j) (= k! (+ k c2)) (= c1! c1) (= c2! c2) (= n! n) (= v! 1))))
(define-fun post_fun ((i Int) (j Int) (k Int) (c1 Int) (c2 Int) (n Int) (v Int)) Bool
    (=> (>= i n) (> k n)))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

