(set-logic LIA)

(synth-inv inv-f ((x Int) (y Int)))

(declare-primed-var x Int)
(declare-primed-var y Int)

(define-fun pre-f ((x Int) (y Int)) Bool
(and (<= x 5) (>= x 4) (<= y 5) (>= y 4) ))

(define-fun trans-f ((x Int) (y Int) (x! Int) (y! Int)) Bool
(or (and (= x! (- x 1)) (= y! y) (>= x 0 ) (>= y 0) )
(and (= x! x) (= y! (- y 1)) (< x 0) (>= y 0) )
(and (= x! (+ x 1)) (= y! (- y 1)) (< y 0) )))

(define-fun post-f ((x Int) (y Int)) Bool
(and (<= y 5) ))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)
