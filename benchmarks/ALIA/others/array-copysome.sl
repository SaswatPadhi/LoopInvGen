(set-logic ALIA)

(synth-inv inv_fun ((a1 (Array Int Int)) (a2 (Array Int Int)) (n Int) (i Int) (z Int)))

(define-fun pre_fun ((a1 (Array Int Int)) (a2 (Array Int Int)) (n Int) (i Int) (z Int)) Bool
    (and (= i 0) (and (> n 0) (and (< i n) (and (>= z 0) (< z n))))))
(define-fun trans_fun ((a1 (Array Int Int)) (a2 (Array Int Int)) (n Int) (i Int) (z Int) (a1! (Array Int Int)) (a2! (Array Int Int)) (n! Int) (i! Int) (z! Int)) Bool
    (and (< i n) (= i! (+ i 1)) (and (= n! n) (and (= z! z) (and (= a2! a2) (or (and (= i z) (= (select a1! i) (select a1 i))) (and (not (= i z)) (= a1! (store a1 i (select a2 i))))))))))
(define-fun post_fun ((a1 (Array Int Int)) (a2 (Array Int Int)) (n Int) (i Int) (z Int)) Bool
    (or (< i n) (forall ((x Int)) (=> (and (>= x 0) (< x n)) (or (not (not (= x z))) (= (select a1 x) (select a2 x)))))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

