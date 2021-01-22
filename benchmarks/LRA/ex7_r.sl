(set-logic LRA)

(synth-inv inv_fun ((x Real) (y Real) (i Real)))

(define-fun pre_fun ((x Real) (y Real) (i Real)) Bool
    (and (and (and (= i 0.) (>= x 0.)) (>= y 0.)) (>= x y)))
(define-fun trans_fun ((x Real) (y Real) (i Real) (x! Real) (y! Real) (i! Real)) Bool
    (and (and (< i y) (= i! (+ i 1.))) (and (= y! y) (= x! x))))
(define-fun post_fun ((x Real) (y Real) (i Real)) Bool
    (not (and (< i y) (or (>= i x) (> 0. i)))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)