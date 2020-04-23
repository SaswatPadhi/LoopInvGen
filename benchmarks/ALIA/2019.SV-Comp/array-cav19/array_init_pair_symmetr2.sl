(set-logic ALIA)

(synth-inv inv_fun ((a (Array Int Int)) (b (Array Int Int)) (c (Array Int Int)) (x Int) (y Int) (n Int) (i Int)))

(define-fun pre_fun ((a (Array Int Int)) (b (Array Int Int)) (c (Array Int Int)) (x Int) (y Int) (n Int) (i Int)) Bool
    (and (>= n 0) (= i 0)))
(define-fun trans_fun ((a (Array Int Int)) (b (Array Int Int)) (c (Array Int Int)) (x Int) (y Int) (n Int) (i Int) (a! (Array Int Int)) (b! (Array Int Int)) (c! (Array Int Int)) (x! Int) (y! Int) (n! Int) (i! Int)) Bool
    (and (< i n) (= i! (+ i 1)) (= n! n) (> x! (- 100000)) (< x! 100000) (> y! (- 100000)) (< y! 100000) (> x! y!) (= a! (store a i x!)) (= b! (store b i y!)) (= c! (store c i (- (select a i) (select b i))))))
(define-fun post_fun ((a (Array Int Int)) (b (Array Int Int)) (c (Array Int Int)) (x Int) (y Int) (n Int) (i Int)) Bool
    (or (< i n) (forall ((j Int)) (=> (and (>= j 0) (=> (< j n))) (> (select c j) 0)))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

