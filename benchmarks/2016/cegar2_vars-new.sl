(set-logic LIA)

(synth-inv inv-f ((x Int) (n Int) (m Int) (z1 Int) (z2 Int) (z3 Int)))

(declare-primed-var x Int)
(declare-primed-var n Int)
(declare-primed-var m Int)
(declare-primed-var z1 Int)
(declare-primed-var z2 Int)
(declare-primed-var z3 Int)

(define-fun pre-f ((x Int) (n Int) (m Int) (z1 Int) (z2 Int) (z3 Int)) Bool
(and (= x 1) (= m 1)))

(define-fun trans-f ((x Int) (n Int) (m Int) (z1 Int) (z2 Int) (z3 Int) (x! Int) (n! Int) (m! Int) (z1! Int) (z2! Int) (z3! Int)) Bool
(or
(and (and (and (< x n) (= x! (+ x 1))) (= n! n)) (= m! m))

(and (and (and (< x n) (= x! (+ x 1))) (= n! n)) (= m! x))))


(define-fun post-f ((x Int) (n Int) (m Int) (z1 Int) (z2 Int) (z3 Int)) Bool
(not (and (and (>= x n) (> n 1))
(or (<= n m) (< m 1)))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)