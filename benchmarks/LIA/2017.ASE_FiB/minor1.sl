(set-logic LIA)

(synth-inv inv_fun ((x Int) ))

(declare-primed-var x Int)

(define-fun pre_fun ((x Int)) Bool
(and (<= x -2) (>= x -3) ))

(define-fun trans_fun ((x Int) (x! Int)) Bool
(or (and (= x! (+ x 2)) (< x 1) )
(and (= x! (+ x 1)) (>= x 1) )))

(define-fun post_fun ((x Int)) Bool
(and (>= x -5)))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)
