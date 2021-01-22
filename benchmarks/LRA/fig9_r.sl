(set-logic LRA)

(synth-inv inv_fun ((x Real) (y Real)))

(define-fun pre_fun ((x Real) (y Real)) Bool
    (and (= x 0.) (= y 0.)))
(define-fun trans_fun ((x Real) (y Real) (x! Real) (y! Real)) Bool
    (and (= x! x) (and (<= 0. y) (= y! (+ x y)))))
(define-fun post_fun ((x Real) (y Real)) Bool
    (>= y 0.))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)