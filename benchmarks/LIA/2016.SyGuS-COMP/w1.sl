(set-logic LIA)

(synth-inv inv-f ((x Int) (n Int)))

(declare-primed-var x Int)
(declare-primed-var n Int)

(define-fun pre-f ((x Int) (n Int)) Bool
(and (= x 0) (>= n 0)))

(define-fun trans-f ((x Int) (n Int) (x! Int) (n! Int) ) Bool
(and (= n! n) (and (< x n) (= x! (+ x 1)))))

(define-fun post-f ((x Int) (n Int)) Bool
(or (not (>= x n)) (= x n)))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)