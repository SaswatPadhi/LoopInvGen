(set-logic LRA)

(synth-inv inv_fun ((x Real) (y Real)))

(define-fun pre_fun ((x Real) (y Real)) Bool
    (and (= x 1.0) (= y 0.0)))
(define-fun trans_fun ((x Real) (y Real) (x! Real) (y! Real)) Bool
    (and (and (< y 1000.0) (= x! (+ x y))) (= y! (+ y 1.0))))
(define-fun post_fun ((x Int) (y Int)) Bool
    (not (and (>= y 1000) (< x y))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)