(set-logic LIA)

(synth-inv inv_fun ((x Int) (y Int)))

(define-fun pre_fun ((x Int) (y Int)) Bool
    (and (= x 1) (= y 0)))
(define-fun trans_fun ((x Int) (y Int) (x! Int) (y! Int)) Bool
    (and (and (< y 100000) (= x! (+ x y))) (= y! (+ y 1))))
(define-fun post_fun ((x Int) (y Int)) Bool
    (not (and (>= y 100000) (< x y))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

