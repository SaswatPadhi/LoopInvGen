(set-logic LIA)

(synth-inv inv-f ((i Int) (t Int) (x Int) (y Int)))

(declare-primed-var i Int)
(declare-primed-var t Int)
(declare-primed-var x Int)
(declare-primed-var y Int)

(define-fun pre-f ((i Int) (t Int) (x Int) (y Int)) Bool
(and (not (= x y)) (= i 0) (= t y)))

(define-fun trans-f ((i Int) (t Int) (x Int) (y Int) (i! Int) (t! Int) (x! Int) (y! Int)) Bool
(or 
(and (> x 0) (= i! i) (= t! t) (= x! x) (= y! (+ x y)))
(and (<= x 0) (= i! i) (= t! t) (= x! x) (= y! y))
))

(define-fun post-f ((i Int) (t Int) (x Int) (y Int)) Bool
(>= y t))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)
