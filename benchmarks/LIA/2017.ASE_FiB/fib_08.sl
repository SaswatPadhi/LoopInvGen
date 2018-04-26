(set-logic LIA)

(synth-inv inv-f ((x Int) (y Int)))

(declare-primed-var x Int)
(declare-primed-var y Int)

(define-fun pre-f ((x Int) (y Int)) Bool
(and (= x 0) (= y 0) ))

(define-fun trans-f ((x Int) (y Int) (x! Int) (y! Int)) Bool
(or (and (= x! (+ x 1)) (= y! (+ y 100)))
(and (>= x 4) (= x! (+ x 1)) (= y! (+ y 1)))
(and (< x 0) (= x! x) (= y! (- y 1)))
(and (= x! x) (= y! y))
))

(define-fun post-f ((x Int) (y Int)) Bool
(or (< x 4) (> y 2)) )

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)
