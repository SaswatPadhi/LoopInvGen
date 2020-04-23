(set-logic ALIA)

(synth-inv inv_fun ((a (Array Int Int)) (n Int) (j Int) (i Int) (x Int) (k Int)))

(define-fun pre_fun ((a (Array Int Int)) (n Int) (j Int) (i Int) (x Int) (k Int)) Bool
    (and (>= n 0) (= i 0) (= j 0) (= k 0)))
(define-fun trans_fun ((a (Array Int Int)) (n Int) (j Int) (i Int) (x Int) (k Int) (a! (Array Int Int)) (n! Int) (j! Int) (i! Int) (x! Int) (k! Int)) Bool
    (and (and (< i n) (= x 0)) (= n! n) (= k! (- k i)) (= j! (+ j i)) (= a! (store a i j))))
(define-fun post_fun ((a (Array Int Int)) (n Int) (j Int) (i Int) (x Int) (k Int)) Bool
    (or (and (< i n) (= x 0)) (forall ((l Int)) (=> (and (> l 0) (< l i)) (>= (select a l) k)))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

