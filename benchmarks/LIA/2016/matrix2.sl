(set-logic LIA)

(synth-inv inv-f ((m Int) (a Int) (j Int) (k Int)))

(declare-primed-var m Int)
(declare-primed-var a Int)
(declare-primed-var j Int)
(declare-primed-var k Int)

(define-fun pre-f ((m Int) (a Int) (j Int) (k Int)) Bool
(and (or (<= a m) (= j 0)) (and (< j 1) (= k 0))))

(define-fun trans-f ((m Int) (a Int) (j Int) (k Int) (m! Int) (a! Int) (j! Int) (k! Int)) Bool
(or (and (= j! j) (and (< k 1) (and (< m a!) (and (= m! a!) (= k! (+ k 1))))))
(and (= j! j) (and (< k 1) (and (> m a!) (= k! (+ k 1)))))))

(define-fun post-f ((m Int) (a Int) (j Int) (k Int)) Bool
(or (< k 1) (or (< a m) (= j -1))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)