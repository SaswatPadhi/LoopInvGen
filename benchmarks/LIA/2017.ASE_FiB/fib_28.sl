(set-logic LIA)

(synth-inv inv_fun ((n Int) (x Int) (y Int)))

(declare-primed-var n Int)
(declare-primed-var x Int)
(declare-primed-var y Int)

(define-fun pre_fun ((n Int) (x Int) (y Int)) Bool
(and (= n 0) (>= x 0) (>= y 0) (= x y)))

(define-fun trans_fun ((n Int) (x Int) (y Int) (n! Int) (x! Int) (y! Int)) Bool
(or 
(and (= x n) (= n! n) (= x! x) (= y! y))
(and (not (= x n)) (= n! n) (= x! (- x 1)) (= y! (- y 1)))
))

(define-fun post_fun ((n Int) (x Int) (y Int)) Bool
(=> (= x n) (= y n)))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)
