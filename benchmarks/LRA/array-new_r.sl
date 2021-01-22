(set-logic LRA)

(synth-inv inv_fun ((x Real) (y Real) (z Real)))

(define-fun pre_fun ((x Real) (y Real) (z Real)) Bool
    (= x 0.))
(define-fun trans_fun ((x Real) (y Real) (z Real) (x! Real) (y! Real) (z! Real)) Bool
    (or (and (= x! (+ x 1.)) (and (= y! z!) (and (<= z! y) (< x 500.)))) (and (= x! (+ x 1.)) (and (= y! y) (and (> z! y) (< x 500.))))))
(define-fun post_fun ((x Int) (y Int) (z Int)) Bool
    (not (and (>= x 500.) (< z y))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)