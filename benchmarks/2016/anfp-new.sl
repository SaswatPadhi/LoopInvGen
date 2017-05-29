(set-logic LIA)

(synth-inv inv-f ((x Int) (y Int)))

(declare-primed-var x Int)
(declare-primed-var y Int)

(define-fun pre-f ((x Int) (y Int)) Bool
(and (= x 1)  
(= y 0)))

(define-fun trans-f ((x Int) (y Int) (x! Int) (y! Int) ) Bool
(and (and (< y 100000) (= x! (+ x y))) (= y! (+ y 1))))

(define-fun post-f ((x Int) (y Int)) Bool
(not (and (>= y 100000) (< x y))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)