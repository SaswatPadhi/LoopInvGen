(set-logic ALIA)

(synth-inv inv_fun ((a (Array Int Int)) (n Int) (i Int) (j Int) (k Int)))

(define-fun pre_fun ((a (Array Int Int)) (n Int) (i Int) (j Int) (k Int)) Bool
    (and (< n 100000) (> j 0) (< j 10000) (= i 1)))
(define-fun trans_fun ((a (Array Int Int)) (n Int) (i Int) (j Int) (k Int) (a! (Array Int Int)) (n! Int) (i! Int) (j! Int) (k! Int)) Bool
    (and (< i n) (= i! (+ i 1)) (= n! n) (> k! 0) (< k! 10000) (= a! (store a i (+ i j k!)))))
(define-fun post_fun ((a (Array Int Int)) (n Int) (i Int) (j Int) (k Int)) Bool
    (or (< i n) (forall ((m Int)) (=> (and (> m 0) (< m n)) (>= (select a m) (+ m 2))))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

