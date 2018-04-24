(set-logic LIA)

(synth-inv inv-f ((c Int) (n Int)))

(declare-primed-var c Int)
(declare-primed-var n Int)

(define-fun pre-f ((c Int) (n Int)) Bool
(and (= c 0) (> n 0)))

(define-fun trans-f ((c Int) (n Int) (c! Int) (n! Int)) Bool
(or
(and (and (> c n) (= c! (+ c 1))) (= n! n))
(and (and (= c n) (= c! 1)) (= n! n))
)
)

(define-fun post-f ((c Int) (n Int)) Bool
(and 
(or (= c n) (and (>= c 0) (<= c n)))
(or (not (= c n)) (> n -1))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)