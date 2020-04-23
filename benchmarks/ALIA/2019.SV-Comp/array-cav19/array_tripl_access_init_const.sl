(set-logic ALIA)

(synth-inv inv_fun ((a (Array Int Int)) (n Int) (i Int)))

(define-fun pre_fun ((a (Array Int Int)) (n Int) (i Int)) Bool
    (and (>= n 0) (= i 0)))
(define-fun trans_fun ((a (Array Int Int)) (n Int) (i Int) (a! (Array Int Int)) (n! Int) (i! Int)) Bool
    (and (<= i n) (= i! (+ i 1)) (= n! n) (= a! (store (store (store a (* 3 i) 0) (+ 1 (* 3 i)) 0) (+ 2 (* 3 i)) 0))))
(define-fun post_fun ((a (Array Int Int)) (n Int) (i Int)) Bool
    (or (<= i n) (forall ((j Int)) (=> (and (>= j 0) (<= j (* 3 n))) (>= 0 (select a j))))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

