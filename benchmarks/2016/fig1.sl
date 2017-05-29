(set-logic LIA)

(synth-inv inv-f ((x Int) (y Int)))

(declare-primed-var x Int)
(declare-primed-var y Int)

(define-fun pre-f ((x Int) (y Int)) Bool
(= x -50))

(define-fun trans-f ((x Int) (y Int) (x! Int) (y! Int)) Bool
(and (and (< x 0) (= x! (+ x y))) (= y! (+ y 1))))

(define-fun post-f ((x Int) (y Int)) Bool
(not (and (>= x 0) (<= y 0))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)