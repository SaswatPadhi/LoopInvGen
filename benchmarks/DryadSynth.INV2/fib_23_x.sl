(set-logic LIA)

(synth-inv inv-f ((i Int) (sum Int) (n Int)))

(declare-primed-var i Int)
(declare-primed-var sum Int)
(declare-primed-var n Int)

(define-fun pre-f ((i Int) (sum Int) (n Int)) Bool
(and (= sum 0) (>= n 0) (= i 0)))

(define-fun trans-f ((i Int) (sum Int) (n Int) (i! Int) (sum! Int) (n! Int)) Bool
(or 
(and (< i n) (= i! (+ i 1)) (= sum! (+ sum i)) (= n! n))
(and (>= i n) (= i! i) (= sum! sum) (= n! n))
))

(define-fun post-f ((i Int) (sum Int) (n Int)) Bool
(=> (>= i n) (>= sum 0)))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)
