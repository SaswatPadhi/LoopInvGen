(set-logic LIA)

(synth-inv inv-f ((x Int) (m Int) (n Int)))

(declare-primed-var x Int)
(declare-primed-var m Int)
(declare-primed-var n Int)

(define-fun pre-f ((x Int) (m Int) (n Int)) Bool
(and (= x 0) (= m 0) (> n 0)))

(define-fun trans-f ((x Int) (m Int) (n Int) (x! Int) (m! Int) (n! Int)) Bool
(or 
(and (>= x n) (= x! x) (= m! m) (= n! n))
(and (< x n) (= x! (+ x 1)) (= m! x) (= n! n))
(and (< x n) (= x! (+ x 1)) (= m! m) (= n! n))
))

(define-fun post-f ((x Int) (m Int) (n Int)) Bool
(=> (>= x n) (or (<= n 0) (and (<= 0 m) (< m n) ) )))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)
