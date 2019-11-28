(set-logic ALIA)

(synth-inv inv_fun ((a (Array Int Int)) (n Int) (j Int) (i Int) (x Int)))

(declare-primed-var a (Array Int Int))
(declare-primed-var j Int)
(declare-primed-var i Int)
(declare-primed-var n Int)
(declare-primed-var x Int)


(define-fun pre_fun ((a (Array Int Int)) (n Int) (j Int) (i Int) (x Int)) Bool
  (and (>= n 0) (= i 0) (= j 0)))

(define-fun trans_fun ((a (Array Int Int)) (n Int) (j Int) (i Int) (x Int) (a! (Array Int Int)) (n! Int) (j! Int) (i! Int) (x! Int)) Bool
  (and (and (< i n) (= x 0))
       (= n! n)
       (= a! (store a i j))
       (= j! (- j i))
  )
)

(define-fun post_fun ((a (Array Int Int)) (n Int) (j Int) (i Int) (x Int)) Bool
  (or (and (< i n) (= x 0))
      (forall ((l Int)) (=> (and (>= l 4) (< l i))
                            (<= (select a l) 0)))
  )
)

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)