(set-logic ALIA)

(synth-inv inv_fun ((a (Array Int Int)) (b (Array Int Int)) (n Int) (i Int) (i1 Int) (sum Int)))

(define-fun pre_fun ((a (Array Int Int)) (b (Array Int Int)) (n Int) (i Int) (i1 Int) (sum Int)) Bool
    (and (>= n 0) (= i 0) (= sum 0) (= i1 0)))
(define-fun trans_fun ((a (Array Int Int)) (b (Array Int Int)) (n Int) (i Int) (i1 Int) (sum Int) (a! (Array Int Int)) (b! (Array Int Int)) (n! Int) (i! Int) (i1! Int) (sum! Int)) Bool
    (and (< i1 (* 2 n)) (= i1! (+ i1! 1)) (= n! n) (ite (< i1 n) (and (< i n) (= i! (+ i 1)) (= a! (store a i i)) (= b! (store b (+ n (- i) (- 1)) i))) (= sum! (+ sum (- (select a (- i1 n)) (select b (+ n (- (- i1 n)) (- 1)))))))))
(define-fun post_fun ((a (Array Int Int)) (b (Array Int Int)) (n Int) (i Int) (i1 Int) (sum Int)) Bool
    (or (< i1 (* 2 n)) (= sum 0)))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

