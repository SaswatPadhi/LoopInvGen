(set-logic LIA)

(synth-inv inv-f ((x Int) (n Int) (v1 Int) (v2 Int) (v3 Int)))

(declare-primed-var x Int)
(declare-primed-var n Int)
(declare-primed-var v1 Int)
(declare-primed-var v2 Int)
(declare-primed-var v3 Int)

(define-fun pre-f ((x Int) (n Int) (v1 Int) (v2 Int) (v3 Int)) Bool
(= x n))

(define-fun trans-f ((x Int) (n Int) (v1 Int) (v2 Int) (v3 Int) (x! Int) (n! Int) (v1! Int) (v2! Int) (v3! Int)) Bool
(and (and (> x 1) (= x! (- x 1))) (= n! n)))

(define-fun post-f ((x Int) (n Int) (v1 Int) (v2 Int) (v3 Int)) Bool
(not (and (<= x 1) (and (not (= x 1)) (>= n 0)))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)