(set-logic LIA)

(synth-inv inv-f ((c Int)))

(declare-primed-var c Int)

(define-fun pre-f ((c Int)) Bool
(= c 0))

(define-fun trans-f ((c Int) (c! Int)) Bool
(or
(and (not (= c 40)) (= c! (+ c 1)))
(and (= c 40) (= c! 1))))

(define-fun post-f ((c Int)) Bool
(not (and (not (= c 40)) (or (< c 0) (> c 40)))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)