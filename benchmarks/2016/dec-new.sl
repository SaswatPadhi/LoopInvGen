(set-logic LIA)

(synth-inv inv-f ((x Int)))

(declare-primed-var x Int)

(define-fun pre-f ((x Int)) Bool
(= x 10000))

(define-fun trans-f ((x Int) (x! Int)) Bool
(and (> x 0) (= x! (- x 1))))

(define-fun post-f ((x Int)) Bool
(not (and (<= x 0) (not (= x 0)))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)