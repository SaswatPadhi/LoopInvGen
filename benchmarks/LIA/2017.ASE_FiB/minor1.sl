(set-logic LIA)

(synth-inv inv-f ((x Int) ))

(declare-primed-var x Int)

(define-fun pre-f ((x Int)) Bool
(and (<= x -2) (>= x -3) ))

(define-fun trans-f ((x Int) (x! Int)) Bool
(or (and (= x! (+ x 2)) (< x 1) )
(and (= x! (+ x 1)) (>= x 1) )))

(define-fun post-f ((x Int)) Bool
(and (>= x -5)))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)
