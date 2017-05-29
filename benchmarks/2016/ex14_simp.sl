(set-logic LIA)

(synth-inv inv-f ((x Int) (y Int) (n Int)))

(declare-primed-var x Int)
(declare-primed-var y Int)
(declare-primed-var n Int)

(define-fun pre-f ((x Int) (y Int) (n Int)) Bool
(= x 1))  


(define-fun trans-f ((x Int) (y Int) (n Int) (x! Int) (y! Int) (n! Int)) Bool
(and (and (<= x n) (= y! (- n x)))
(= x! (+ x 1))))

(define-fun post-f ((x Int) (y Int) (n Int)) Bool
(not (and (and (<= x n) (= y (- n x))) 
(or (>= y n) (> 0 y)))))


(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)