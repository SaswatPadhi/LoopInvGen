(set-logic LIA)

(synth-inv inv-f ((n Int) (x Int) (y Int)))

(declare-primed-var n Int)
(declare-primed-var x Int)
(declare-primed-var y Int)

(define-fun pre-f ((n Int) (x Int) (y Int)) Bool
(and (= n 0) (>= x 0) (>= y 0) (= x y)))

(define-fun trans-f ((n Int) (x Int) (y Int) (n! Int) (x! Int) (y! Int)) Bool
(or 
(and (= x n) (= n! n) (= x! x) (= y! y))
(and (not (= x n)) (= n! n) (= x! (- x 1)) (= y! (- y 1)))
))

(define-fun post-f ((n Int) (x Int) (y Int)) Bool
(=> (= x n) (= y n)))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)
