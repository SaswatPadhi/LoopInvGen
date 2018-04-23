(set-logic LIA)

(synth-inv inv-f ((x Int) (n Int) (m Int)))

(declare-primed-var x Int)
(declare-primed-var n Int)
(declare-primed-var m Int)

(define-fun pre-f ((x Int) (n Int) (m Int)) Bool
(and (= x 1) (= m 1)))

(define-fun trans-f ((x Int) (n Int) (m Int) (x! Int) (n! Int) (m! Int)) Bool
(or
(and (and (and (< x n) (= x! (+ x 1))) (= n! n)) (= m! m))

(and (and (and (< x n) (= x! (+ x 1))) (= n! n)) (= m! x))))


(define-fun post-f ((x Int) (n Int) (m Int)) Bool
(not (and (and (>= x n) (> n 1))
(or (<= n m) (< m 1)))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)