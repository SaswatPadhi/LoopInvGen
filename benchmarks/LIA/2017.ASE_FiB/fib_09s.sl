(set-logic LIA)

(synth-inv inv_fun ((i Int) (pvlen Int) (t Int) (k Int) (n Int) (j Int) (turn Int)))

(declare-primed-var i Int)
(declare-primed-var pvlen Int)
(declare-primed-var t Int)
(declare-primed-var k Int)
(declare-primed-var n Int)
(declare-primed-var j Int)
(declare-primed-var turn Int)

(define-fun pre_fun ((i Int) (pvlen Int) (t Int) (k Int) (n Int) (j Int) (turn Int)) Bool
(and (= k 0) (= i 0) (= turn 0)
))

(define-fun trans_fun ((i Int) (pvlen Int) (t Int) (k Int) (n Int) (j Int) (turn Int) (i! Int) (pvlen! Int) (t! Int) (k! Int) (n! Int) (j! Int) (turn! Int)) Bool
(or (and (= turn 0) (= i! (+ i 1)) (= pvlen! pvlen) (= t! t) (= k! k) (= n! n) (= j! j) (= turn! 0))
(and (= turn 0) (= i! (+ i 1)) (= pvlen! pvlen) (= t! t) (= k! k) (= n! n) (= j! j) (= turn! 1))
(and (= turn 1) (> i pvlen) (= i! 0) (= pvlen! i) (= t! t) (= k! k) (= n! n) (= j! j) (= turn! 2))
(and (= turn 1) (<= i pvlen) (= i! 0) (= pvlen! pvlen) (= t! t) (= k! k) (= n! n) (= j! j) (= turn! 2))
(and (= turn 2) (= i! (+ i 1)) (= pvlen! pvlen) (= t! i) (= k! (+ k 1)) (= n! n) (= j! j) (= turn! 2))
(and (= turn 2) (= i! (+ i 1)) (= pvlen! pvlen) (= t! i) (= k! (+ k 1)) (= n! n) (= j! j) (= turn! 3))
(and (= turn 3) (= i! i) (= pvlen! pvlen) (= t! t) (= k! k) (= n! n) (= j! j) (= turn! 3))
(and (= turn 3) (= i! i) (= pvlen! pvlen) (= t! t) (= k! k) (= n! n) (= j! j) (= turn! 4))
(and (= turn 4) (= i! i) (= pvlen! pvlen) (= t! t) (= k! k) (= n! i) (= j! 0) (= turn! 5))
))

(define-fun post_fun ((i Int) (pvlen Int) (t Int) (k Int) (n Int) (j Int) (turn Int)) Bool
(>= k 0))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)
