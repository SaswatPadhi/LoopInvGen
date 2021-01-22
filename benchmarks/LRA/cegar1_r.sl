(set-logic LRA)

(synth-inv inv_fun ((x Real) (y Real)))

(define-fun pre_fun ((x Real) (y Real)) Bool
    (and (and (>= x 0.) (and (<= x 2.) (<= y 2.))) (>= y 0.)))
(define-fun trans_fun ((x Real) (y Real) (x! Real) (y! Real)) Bool
    (and (= x! (+ x 2.)) (= y! (+ y 2.))))
(define-fun post_fun ((x Real) (y Real)) Bool
    (not (and (= x 4.) (= y 0.))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)