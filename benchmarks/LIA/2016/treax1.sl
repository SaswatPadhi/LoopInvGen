(set-logic LIA)

(synth-inv inv-f ((x Int) (y Int)))

(declare-primed-var x Int)
(declare-primed-var y Int)

(define-fun pre-f ((x Int) (y Int)) Bool
(= x 1))


(define-fun trans-f ((x Int) (y Int) (x! Int) (y! Int) ) Bool
(and (< x y) (= x! (+ x x))))

(define-fun post-f ((x Int) (y Int)) Bool
(or (not (>= x y)) (>= x 1)))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)