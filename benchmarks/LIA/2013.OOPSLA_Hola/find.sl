#need to change this based on having a aux var that tracks if we found

(set-logic ALIA)

(synth-inv inv_fun ((a (Array Int Int)) (e Int) (n Int) (i Int)))
(declare-primed-var a (Array Int Int))
(declare-primed-var i Int)
(declare-primed-var n Int)
(declare-primed-var e Int)

(define-fun pre_fun ((a (Array Int Int)) (n Int) (i Int) (e Int)) Bool
  (and (>= n 0)
       (= i 0)
       (< i n)
  )
)

(define-fun trans_fun ((a (Array Int Int)) (n Int) (i Int) (e Int) (a! (Array Int Int)) (e! Int) (n! Int) (i! Int)) Bool
 (and (= i! (+ i 1))
 
      (= n! n)
      (= a! a)
      (= e! e)
      (not (= e! (select a i)))
 ))

(define-fun post_fun ((a (Array Int Int)) (e Int) (n Int) (i Int)) Bool
  (or (> i n) (= e (select a i)))
)

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)