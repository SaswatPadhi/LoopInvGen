(set-logic ALIA)

(synth-inv inv_fun ((a (Array Int Int)) (n Int) (j Int) (i Int) (x Int) (k Int)))

(declare-primed-var a (Array Int Int))
(declare-primed-var j Int)
(declare-primed-var i Int)
(declare-primed-var n Int)
(declare-primed-var x Int)
(declare-primed-var k Int)


(define-fun pre_fun ((a (Array Int Int)) (n Int) (j Int) (i Int) (x Int) (k Int)) Bool
  (and (>= n 0) (= i 0) (= j 0) (= k 0)))

(define-fun trans_fun ((a (Array Int Int)) (n Int) (j Int) (i Int) (x Int) (k Int) (a! (Array Int Int)) (n! Int) (j! Int) (i! Int) (x! Int) (k! Int)) Bool
  (and (and (< i n) (= x 0))
       (= n! n)
       (= k! (- k 1))
       (= j! (+ j 1))
       (= a! (store a i j))
  )
)

(define-fun post_fun ((a (Array Int Int)) (n Int) (j Int) (i Int) (x Int)) Bool
  (or (and (< i n) (= x 0))
      (forall ((l Int)) (=> (and (>= l 0) (< l i))
                            (>= k (select a l))))
  )
)

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)