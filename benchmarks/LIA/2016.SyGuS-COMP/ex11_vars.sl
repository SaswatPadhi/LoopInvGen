(set-logic LIA)

(synth-inv inv-f ((c Int) (n Int) (v1 Int) (v2 Int) (v3 Int)))

(declare-primed-var c Int)
(declare-primed-var n Int)
(declare-primed-var v1 Int)
(declare-primed-var v2 Int)
(declare-primed-var v3 Int)

(define-fun pre-f ((c Int) (n Int) (v1 Int) (v2 Int) (v3 Int)) Bool
(and (= c 0) (> n 0)))

(define-fun trans-f ((c Int) (n Int) (v1 Int) (v2 Int) (v3 Int) (c! Int) (n! Int) (v1! Int) (v2! Int) (v3! Int)) Bool
(or
(and (not (= c n)) (= c! (+ c 1)))
(and (= c n) (= c! 1))))

(define-fun post-f ((c Int) (n Int) (v1 Int) (v2 Int) (v3 Int)) Bool
(not (or (and (not (= c n)) (or (< c 0) (> c n)))
(and (= c n) (> n -1)))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)