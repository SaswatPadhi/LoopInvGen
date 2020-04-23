(set-logic ALIA)

(synth-inv inv_fun ((a (Array Int Int)) (n Int) (j Int) (i Int) (x Int)))

(define-fun pre_fun ((a (Array Int Int)) (n Int) (j Int) (i Int) (x Int)) Bool
    (and (>= n 0) (= i 0) (= j 0)))
(define-fun trans_fun ((a (Array Int Int)) (n Int) (j Int) (i Int) (x Int) (a! (Array Int Int)) (n! Int) (j! Int) (i! Int) (x! Int)) Bool
    (and (and (< i n) (= x 0)) (= n! n) (= j! (+ j i)) (= a! (store a i j))))
(define-fun post_fun ((a (Array Int Int)) (n Int) (j Int) (i Int) (x Int)) Bool
    (or (and (< i n) (= x 0)) (forall ((k Int)) (=> (and (> k 0) (< k i)) (>= (select a k) 0)))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

