(set-logic LIA)

(synth-inv inv-f ((j Int) (k Int) (t Int)))

(declare-primed-var j Int)
(declare-primed-var k Int)
(declare-primed-var t Int)

(define-fun pre-f ((j Int) (k Int) (t Int)) Bool
(and (= j 2) (= k 0) ))

(define-fun trans-f ((j Int) (k Int) (t Int) (j! Int) (k! Int) (t! Int)) Bool
(or  (and  (= t 0) (= j! (+ j 4)) (= k! k) (= t! t))
(and (not (= t 0)) (= j! (+ j 2)) (= k! (+ k 1)) (= t! t ))
))

(define-fun post-f ((j Int) (k Int) (t Int)) Bool
(or (= k 0) (= j (+ (* k 2) 2) )))


(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)
