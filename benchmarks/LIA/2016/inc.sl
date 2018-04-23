(set-logic LIA)

(synth-inv inv-f ((x Int)))

(declare-primed-var x Int)

(define-fun pre-f ((x Int)) Bool
(= x 0))


(define-fun trans-f ((x Int) (x! Int)) Bool
(and (< x 100) (= x! (+ x 1))))

(define-fun post-f ((x Int)) Bool
(or (not (>= x 100)) (= x 100)))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)