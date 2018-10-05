(set-logic LIA)

(synth-inv inv_fun ((x Int) (n Int)))

(declare-primed-var x Int)
(declare-primed-var n Int)

(define-fun pre_fun ((x Int) (n Int)) Bool
(and (> n 0) (= x 0)))

(define-fun trans_fun ((x Int) (n Int) (x! Int) (n! Int)) Bool
(or 
(and (>= x n) (= x! x) (= n! n))
(and (< x n) (= x! (+ x 1)) (= n! n))
))

(define-fun post_fun ((x Int) (n Int)) Bool
(=> (>= x n) (= x n)))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)
