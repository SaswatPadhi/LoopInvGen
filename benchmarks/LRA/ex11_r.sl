(set-logic LRA)

(synth-inv inv_fun ((x Real) (y Real) (lock Real)))

(define-fun pre_fun ((x Real) (y Real) (lock Real)) Bool
    (or (and (= x y) (= lock 1.)) (and (= (+ x 1.) y) (= lock 0.))))
(define-fun trans_fun ((x Real) (y Real) (lock Real) (x! Real) (y! Real) (lock! Real)) Bool
    (or (and (and (not (= x y)) (= lock! 1.)) (= x! y)) (and (and (and (not (= x y)) (= lock! 0)) (= x! y)) (= y! (+ y 1.)))))
(define-fun post_fun ((x Real) (y Real) (lock Real)) Bool
    (not (and (= x y) (not (= lock 1.)))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)