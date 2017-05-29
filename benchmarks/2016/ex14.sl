(set-logic LIA)

(synth-inv inv-f ((x Int) (y Int)))

(declare-primed-var x Int)
(declare-primed-var y Int)

(define-fun pre-f ((x Int) (y Int)) Bool
(= x 1))  


(define-fun trans-f ((x Int) (y Int) (x! Int) (y! Int)) Bool
(and (and (<= x 10) (= y! (- 10 x)))
(= x! (+ x 1))))

(define-fun post-f ((x Int) (y Int)) Bool
(not (and (and (<= x 10) (= y (- 10 x))) 
(or (>= y 10) (> 0 y)))))


(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)