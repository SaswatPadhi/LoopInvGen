(set-logic LIA)

(synth-inv inv-f ((x1 Int) (x2 Int) (x3 Int) (x4 Int)))

(declare-primed-var x1 Int)
(declare-primed-var x2 Int)
(declare-primed-var x3 Int)
(declare-primed-var x4 Int)

(define-fun pre-f ((x1 Int) (x2 Int) (x3 Int) (x4 Int)) Bool
(and (and (= x1 0) (and (= x2 0) (= x3 0))) (= x4 -1)))


(define-fun trans-f ((x1 Int) (x2 Int) (x3 Int) (x4 Int) (x1! Int) (x2! Int) (x3! Int) (x4! Int)) Bool
(and (<= x1! 0) (and (>= x1! (+ x4! 1)) (and (= x2! x3!) (or (>= x4! 0) (<= x4! x3!))))))

(define-fun post-f ((x1 Int) (x2 Int) (x3 Int) (x4 Int)) Bool
(and (<= x1 0) (and (>= x1 (+ x4 1)) (and (= x2 x3) (or (>= x4 0) (<= x4 x3))))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)