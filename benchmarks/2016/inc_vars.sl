(set-logic LIA)

(synth-inv inv-f ((x Int) (n Int) (v1 Int) (v2 Int) (v3 Int)))

(declare-primed-var x Int)
(declare-primed-var n Int)
(declare-primed-var v1 Int)
(declare-primed-var v2 Int)
(declare-primed-var v3 Int)

(define-fun pre-f ((x Int) (n Int) (v1 Int) (v2 Int) (v3 Int)) Bool
(= x 0))


(define-fun trans-f ((x Int) (n Int) (v1 Int) (v2 Int) (v3 Int) (x! Int) (n! Int) (v1! Int) (v2! Int) (v3! Int) ) Bool
(and (= n! n) (and (< x n) (= x! (+ x 1)))))


(define-fun post-f ((x Int) (n Int) (v1 Int) (v2 Int) (v3 Int)) Bool
(or (not (>= x n)) (or (= x n) (< n 0))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)