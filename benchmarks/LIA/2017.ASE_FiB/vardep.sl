(set-logic LIA)

(synth-inv inv_fun ((x Int) (y Int) (z Int)))

(declare-primed-var x Int)
(declare-primed-var y Int)
(declare-primed-var z Int)

(define-fun pre_fun ((x Int) (y Int) (z Int)) Bool
(and (= x 0) (= y 0) (= z 0)))

(define-fun trans_fun ((x Int) (y Int) (z Int) (x! Int) (y! Int) (z! Int)) Bool
(and (= x! (+ x 1)) (= y! (+ y 2)) (= z! (+ z 3)) ))

(define-fun post_fun ((x Int) (y Int) (z Int)) Bool
(and (>= x 0) (>= y 0) (>= z 0)))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)
