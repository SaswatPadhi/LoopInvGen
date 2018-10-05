(set-logic LIA)

(synth-inv inv_fun ((x Int) (y Int)))

(declare-primed-var x Int)
(declare-primed-var y Int)

(define-fun pre_fun ((x Int) (y Int)) Bool
(and (= x 1) (= y 1) ))

(define-fun trans_fun ((x Int) (y Int) (x! Int) (y! Int)) Bool
(and  (= x! (+ x y)) (= y! (+ x y))  ))

(define-fun post_fun ((x Int) (y Int)) Bool
(>= y 1) )

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)
