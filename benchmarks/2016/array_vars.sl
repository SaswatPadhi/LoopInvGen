(set-logic LIA)

(synth-inv inv-f ((x Int) (y Int) (z Int) (v1 Int) (v2 Int) (v3 Int) (size Int)))

(declare-primed-var x Int)
(declare-primed-var y Int)
(declare-primed-var z Int)
(declare-primed-var v1 Int)
(declare-primed-var v2 Int)
(declare-primed-var v3 Int)
(declare-primed-var size Int)

(define-fun pre-f ((x Int) (y Int) (z Int) (v1 Int) (v2 Int) (v3 Int) (size Int)) Bool
(= x 0))

(define-fun trans-f ((x Int) (y Int) (z Int) (v1 Int) (v2 Int) (v3 Int) (size Int) (x! Int) (y! Int) (z! Int) (v1! Int) (v2! Int) (v3! Int) (size! Int)) Bool
(or 
(and (= x! (+ x 1))
(and (= y! z!)
(and (<= z! y)
(< x size))))

(and (= x! (+ x 1))
(and (= y! y)
(and (> z! y)
(< x size))))
))



(define-fun post-f ((x Int) (y Int) (z Int) (v1 Int) (v2 Int) (v3 Int) (size Int)) Bool
(not (and (and (>= x size) (< z y)) (> size 0))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)