(set-logic LIA)

(synth-inv inv_fun ((i Int) (sum Int) (n Int)))

(define-fun pre_fun ((i Int) (sum Int) (n Int)) Bool
    (and (= sum 0) (>= n 0) (= i 0)))
(define-fun trans_fun ((i Int) (sum Int) (n Int) (i! Int) (sum! Int) (n! Int)) Bool
    (or (and (< i n) (= i! (+ i 1)) (= sum! (+ sum i)) (= n! n)) (and (>= i n) (= i! i) (= sum! sum) (= n! n))))
(define-fun post_fun ((i Int) (sum Int) (n Int)) Bool
    (=> (>= i n) (>= sum 0)))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

