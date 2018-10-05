(set-logic LIA)

(synth-inv inv_fun ((x Int) (y Int) (i Int) (j Int) (turn Int)))

(declare-primed-var x Int)
(declare-primed-var y Int)
(declare-primed-var i Int)
(declare-primed-var j Int)
(declare-primed-var turn Int)

(define-fun pre_fun ((x Int) (y Int) (i Int) (j Int) (turn Int)) Bool
(and (= x 0) (= y 0) (= i 0) (= j 0) (= turn 0)))

(define-fun trans_fun ((x Int) (y Int) (i Int) (j Int) (turn Int) (x! Int) (y! Int) (i! Int) (j! Int) (turn! Int)) Bool
(or 
(and (= turn 0) (= x! x) (= y! y) (= i! i) (= j! j) (= turn! 1))
(and (= turn 0) (= x! x) (= y! y) (= i! i) (= j! j) (= turn! 2))
(and (= turn 1) (= x y) (= x! x) (= y! y) (= i! (+ i 1)) (= j! j) (= turn! 1))
(and (= turn 1) (= x y) (= x! x) (= y! y) (= i! (+ i 1)) (= j! j) (= turn! 2))
(and (= turn 1) (not (= x y)) (= x! x) (= y! y) (= i! i) (= j! (+ j 1)) (= turn! 1))
(and (= turn 1) (not (= x y)) (= x! x) (= y! y) (= i! i) (= j! (+ j 1)) (= turn! 2))
(and (= turn 2) (>= i j) (= x! (+ x 1)) (= y! (+ y 1)) (= i! i) (= j! j) (= turn! 0))
(and (= turn 2) (< i j) (= x! x) (= y! (+ y 1)) (= i! i) (= j! j) (= turn! 0))
))

(define-fun post_fun ((x Int) (y Int) (i Int) (j Int) (turn Int)) Bool
(>= i j))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)
