(set-logic LRA)

(synth-inv inv_fun ((x Real) (y Real)))

(define-fun pre_fun ((x Real) (y Real)) Bool
    (= x 1))
(define-fun trans_fun ((x Real) (y Real) (x! Real) (y! Real)) Bool
    (and (and (<= x 10.) (= y! (- 10. x))) (= x! (+ x 1.))))
(define-fun post_fun ((x Real) (y Real)) Bool
    (not (and (and (<= x 10.) (= y (- 10. x))) (or (>= y 10.) (> 0. y)))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)