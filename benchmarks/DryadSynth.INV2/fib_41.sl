(set-logic LIA)

(synth-inv inv-f ((n Int) (k Int) (i Int) (j Int)))

(declare-primed-var n Int)
(declare-primed-var k Int)
(declare-primed-var i Int)
(declare-primed-var j Int)

(define-fun pre-f ((n Int) (k Int) (i Int) (j Int)) Bool
(and (= j 0) (>= n 0) (= i 0) (or (= k 1) (>= k 0))))

(define-fun trans-f ((n Int) (k Int) (i Int) (j Int) (n! Int) (k! Int) (i! Int) (j! Int)) Bool
(or 
(and (> i n) (= n! n) (= k! k) (= i! i) (= j! j))
(and (<= i n) (= n! n) (= k! k) (= i! (+ i 1)) (= j! (+ j 1)))
))

(define-fun post-f ((n Int) (k Int) (i Int) (j Int)) Bool
(=> (> i n) (> (+ k i j) (* 2 n))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)
