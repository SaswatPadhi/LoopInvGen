(set-logic LIA)

(synth-inv inv-f ((c Int) (i Int)))

(declare-primed-var c Int)
(declare-primed-var i Int)

(define-fun pre-f ((c Int) (i Int)) Bool
(= i 0))

(define-fun trans-f ((c Int) (i Int) (c! Int) (i! Int) ) Bool
(and (> c 48) (and (< c 57) (= i! (+ (+ i i) (- c 48))))))

(define-fun post-f ((c Int) (i Int)) Bool
(or (> c 57) (or (< c 48) (>= i 0))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)