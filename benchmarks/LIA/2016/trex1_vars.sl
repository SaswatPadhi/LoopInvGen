(set-logic LIA)

(synth-inv inv-f ((x Int) (y Int) (z1 Int) (z2 Int) (z3 Int)))

(declare-primed-var x Int)
(declare-primed-var y Int)
(declare-primed-var z1 Int)
(declare-primed-var z2 Int)
(declare-primed-var z3 Int)

(define-fun pre-f ((x Int) (y Int) (z1 Int) (z2 Int) (z3 Int)) Bool
(= x 1))


(define-fun trans-f ((x Int) (y Int) (z1 Int) (z2 Int) (z3 Int) (x! Int) (y! Int) (z1! Int) (z2! Int) (z3! Int)) Bool
(and (< x y) (= x! (+ x x))))

(define-fun post-f ((x Int) (y Int) (z1 Int) (z2 Int) (z3 Int)) Bool
(or (not (>= x y)) (>= x 1)))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)