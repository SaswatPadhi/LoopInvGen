
(synth-inv inv_fun ((x (Array Int Int)) (i Int) (n Int)))

(declare-primed-var x (Array Int Int))
(declare-primed-var i Int)
(declare-primed-var n Int)

(define-fun pre_fun ((x (Array Int Int)) (i Int) (n Int)) Bool
(and (= i 0) (= n 3)))


(define-fun trans_fun ((x (Array Int Int)) (i Int) (n Int) (x! (Array Int Int)) (i! Int) (n! Int)) Bool
(and (= n! n)
     (= i! (+ i 1))
     (< i n)
     (= x! (store x i i))
))

(define-fun post_fun ((x (Array Int Int)) (i Int) (n Int)) Bool
(or 
    (< i n)
    (forall ((k Int)) (=> (and (>= k 0)(< k n)) (= k (select x k))))
))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)