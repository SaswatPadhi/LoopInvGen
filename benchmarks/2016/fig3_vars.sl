(set-logic LIA)

(synth-inv inv-f ((x Int) (y Int) (lock Int) (v1 Int) (v2 Int) (v3 Int)))

(declare-primed-var x Int)
(declare-primed-var y Int)
(declare-primed-var lock Int)
(declare-primed-var v1 Int)
(declare-primed-var v2 Int)
(declare-primed-var v3 Int)

(define-fun pre-f ((x Int) (y Int) (lock Int) (v1 Int) (v2 Int) (v3 Int)) Bool
(or (and (= x y) (= lock 1))
(and (= (+ x 1) y) (= lock 0))))


(define-fun trans-f ((x Int) (y Int) (lock Int) (v1 Int) (v2 Int) (v3 Int) (x! Int) (y! Int) (lock! Int) (v1! Int) (v2! Int) (v3! Int)) Bool
(or
(and (and (not (= x y)) (= lock! 1)) (= x! y))
(and (and (and (not (= x y)) (= lock! 0)) (= x! y)) (= y! (+ y 1)))))

(define-fun post-f ((x Int) (y Int) (lock Int) (v1 Int) (v2 Int) (v3 Int)) Bool
(not (and (= x y) (not (= lock 1)))))


(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)