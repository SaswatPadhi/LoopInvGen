(set-logic LIA)

(synth-inv inv_fun ((x Int) (y Int)))

(declare-primed-var x Int)
(declare-primed-var y Int)

(define-fun pre_fun ((x Int) (y Int)) Bool
(and (<= x 1) (>= x 0) (= y -3) ))

(define-fun trans_fun ((x Int) (y Int) (x! Int) (y! Int)) Bool
(or (and (= x! (- x 1)) (= y! (+ y 2)) (< (- x y) 2) )
(and (= x! x) (= y! (+ y 1)) (>= (- x y) 2) )))

(define-fun post_fun ((x Int) (y Int)) Bool
(and (<= x 1) (>= y -3) ))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)
