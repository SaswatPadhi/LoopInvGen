(set-logic ALIA)

(synth-inv inv_fun ((a (Array Int Int)) (b (Array Int Int)) (c (Array Int Int)) (n Int) (i Int)))

(define-fun pre_fun ((a (Array Int Int)) (b (Array Int Int)) (c (Array Int Int)) (n Int) (i Int)) Bool
    (and (>= n 0) (= i 0)))
(define-fun trans_fun ((a (Array Int Int)) (b (Array Int Int)) (c (Array Int Int)) (n Int) (i Int) (a! (Array Int Int)) (b! (Array Int Int)) (c! (Array Int Int)) (n! Int) (i! Int)) Bool
    (and (< i n) (= i! (+ i 1)) (= n! n) (= a! (store a i 1)) (= b! (store b i 2)) (= c! (store c i (+ (select a i) (select b i))))))
(define-fun post_fun ((a (Array Int Int)) (b (Array Int Int)) (c (Array Int Int)) (n Int) (i Int)) Bool
    (or (< i n) (forall ((j Int)) (=> (and (>= j 1) (< j n)) (>= (select c j) 3)))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

