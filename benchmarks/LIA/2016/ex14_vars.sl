(set-logic LIA)

(synth-inv inv-f ((x Int) (y Int) (n Int) (v1 Int) (v2 Int) (v3 Int)))

(declare-primed-var x Int)
(declare-primed-var y Int)
(declare-primed-var n Int)
(declare-primed-var v1 Int)
(declare-primed-var v2 Int)
(declare-primed-var v3 Int)

(define-fun pre-f ((x Int) (y Int) (n Int) (v1 Int) (v2 Int) (v3 Int)) Bool
(= x 1))  


(define-fun trans-f ((x Int) (y Int) (n Int) (v1 Int) (v2 Int) (v3 Int) (x! Int) (y! Int) (n! Int) (v1! Int) (v2! Int) (v3! Int)) Bool
(and (and (<= x n) (= y! (- n x)))
(= x! (+ x 1))))

(define-fun post-f ((x Int) (y Int) (n Int) (v1 Int) (v2 Int) (v3 Int)) Bool
(not (and (and (<= x n) (= y (- n x))) 
(or (>= y n) (> 0 y)))))


(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)