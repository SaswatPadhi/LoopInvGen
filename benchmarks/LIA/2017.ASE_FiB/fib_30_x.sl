(set-logic LIA)

(synth-inv inv-f ((i Int) (c Int) (n Int)))

(declare-primed-var i Int)
(declare-primed-var c Int)
(declare-primed-var n Int)

(define-fun pre-f ((i Int) (c Int) (n Int)) Bool
(and (= i 0) (= c 0) (> n 0)))

(define-fun trans-f ((i Int) (c Int) (n Int) (i! Int) (c! Int) (n! Int)) Bool
(or 
(and (>= i n) (= i! i) (= c! c) (= n! n))
(and (< i n) (= i! (+ i 1)) (= c! (+ c i)) (= n! n))
))

(define-fun post-f ((i Int) (c Int) (n Int)) Bool
(=> (>= i n) (>= c 0)))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)
