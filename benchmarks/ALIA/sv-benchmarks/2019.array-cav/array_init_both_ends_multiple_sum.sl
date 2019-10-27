(set-logic ALIA)

(synth-inv inv_fun ((a (Array Int Int)) (b (Array Int Int)) (n Int) (i Int) (sum Int)))

(declare-primed-var a (Array Int Int))
(declare-primed-var b (Array Int Int))
(declare-primed-var i Int)
(declare-primed-var n Int)
(declare-primed-var sum Int)

(define-fun pre_fun ((a (Array Int Int)) (b (Array Int Int)) (n Int) (i Int) (sum Int)) Bool
  (and (>= n 0) (= i 0) (= sum 0) ))

(define-fun trans_fun ((a (Array Int Int)) (b (Array Int Int)) (n Int) (i Int) (sum Int) (a! (Array Int Int)) (b! (Array Int Int)) (n! Int) (i! Int) (sum! Int)) Bool
  (and (< i n)
       (= i! (+ i 1))
       (= n! n)
       (= a! (store a i i))
       (= b! (store b (+ n (- i) (- 1)) i))
       (= sum! (+ sum (- (select a i) (select b (+ n (- i) (- 1))))))
  )
)

(define-fun post_fun ((a (Array Int Int)) (b (Array Int Int)) (n Int) (i Int) (sum Int)) Bool
  (or (< i n)
      (= sum 0)
  )
)

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)