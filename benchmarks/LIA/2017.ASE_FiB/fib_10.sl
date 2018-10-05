(set-logic LIA)

(synth-inv inv_fun ((x Int) (y Int) (w Int) (z Int)))

(declare-primed-var x Int)
(declare-primed-var y Int)
(declare-primed-var w Int)
(declare-primed-var z Int)

(define-fun pre_fun ((x Int) (y Int) (w Int) (z Int)) Bool
(and (= w 1) (= z 0) (= x 0) (= y 0)))

(define-fun trans_fun ((x Int) (y Int) (w Int) (z Int) (x! Int) (y! Int) (w! Int) (z! Int)) Bool
(or
(and (= w 1) (= z 0) (= x! (+ x 1)) (= w! 0) (= y! (+ y 1)) (= z! 1))
(and (not (= w 1)) (= z 0) (= x! x ) (= w! w) (= y! (+ y 1)) (= z! 1))
(and (= w 1) (not (= z 0)) (= x! (+ x 1)) (= w! 0) (= y! y ) (= z! z))
(and (not (= w 1)) (not (= z 0)) (= x! x ) (= w! w) (= y! y ) (= z! z))
))

(define-fun post_fun ((x Int) (y Int) (w Int) (z Int)) Bool
(= x y))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)
