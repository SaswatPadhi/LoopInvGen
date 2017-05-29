(set-logic LIA)

(synth-inv inv-f ((i Int) (j Int) (x Int) (y Int) (z1 Int) (z2 Int) (z3 Int)))

(declare-primed-var i Int)
(declare-primed-var j Int)
(declare-primed-var x Int)
(declare-primed-var y Int)
(declare-primed-var z1 Int)
(declare-primed-var z2 Int)
(declare-primed-var z3 Int)


(define-fun pre-f ((i Int) (j Int) (x Int) (y Int) (z1 Int) (z2 Int) (z3 Int)) Bool
(and (= i x) (= j y)))


(define-fun trans-f ((i Int) (j Int) (x Int) (y Int) (z1 Int) (z2 Int) (z3 Int) (i! Int) (j! Int) (x! Int) (y! Int) (z1! Int) (z2! Int) (z3! Int)) Bool
(and (= i! i) (and (= j! j) (and (not (= x 0)) (and (= x! (- x 1)) (= y! (- y 1)))))))

(define-fun post-f ((i Int) (j Int) (x Int) (y Int) (z1 Int) (z2 Int) (z3 Int)) Bool
(or (not (= x 0)) (or (not (= i j)) (= y 0))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)