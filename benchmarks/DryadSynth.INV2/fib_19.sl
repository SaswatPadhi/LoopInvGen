(set-logic LIA)

(synth-inv inv-f ((n Int) (m Int) (x Int) (y Int)))

(declare-primed-var n Int)
(declare-primed-var m Int)
(declare-primed-var x Int)
(declare-primed-var y Int)

(define-fun pre-f ((n Int) (m Int) (x Int) (y Int)) Bool
(and (>= n 0) (>= m 0) (< m n) (= x 0) (= y m)))

(define-fun trans-f ((n Int) (m Int) (x Int) (y Int) (n! Int) (m! Int) (x! Int) (y! Int)) Bool
(or 
(and (< x n) (<= (+ x 1) m) (= x! (+ x 1)) (= y! y) (= n! n) (= m! m))
(and (< x n) (> (+ x 1) m) (= x! (+ x 1)) (= y! (+ y 1)) (= n! n) (= m! m))
(and (>= x n) (= x! x) (= y! y) (= n! n) (= m! m))
))

(define-fun post-f ((n Int) (m Int) (x Int) (y Int)) Bool
(=> (not (< x n)) (= y n)))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)
