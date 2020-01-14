(set-logic ALIA)

(synth-inv inv_fun ((a1 (Array Int Int)) (a2 (Array Int Int)) (n Int) (i Int)))

(define-fun pre_fun ((a1 (Array Int Int)) (a2 (Array Int Int)) (n Int) (i Int)) Bool
    (and (>= n 0) (and (= i 0) (< i n))))
(define-fun trans_fun ((a1 (Array Int Int)) (a2 (Array Int Int)) (n Int) (i Int) (a1! (Array Int Int)) (a2! (Array Int Int)) (n! Int) (i! Int)) Bool
    (and (= i! (+ i 1)) (< i n) (= n! n) (= a2! a2) (= 1 (mod i 2)) (= a1! (store a1 i (select a2 i)))))
(define-fun post_fun ((a1 (Array Int Int)) (a2 (Array Int Int)) (n Int) (i Int)) Bool
    (or (< i n) (forall ((j Int)) (=> (and (<= 0 j) (< j n) (= 1 (mod j 2))) (= (select a1 j) (select a2 j))))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

