
(set-logic LRA)

(synth-inv inv_fun ((x Real) (y Real)))

(define-fun pre_fun ((x Real) (y Real)) Bool
    (= x (- 50.)))
(define-fun trans_fun ((x Real) (y Real) (x! Real) (y! Real)) Bool
    (and (and (< x 0.) (= x! (+ x y))) (= y! (+ y 1.))))
(define-fun post_fun ((x Int) (y Int)) Bool
    (not (and (>= x 0.) (<= y 0.))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)