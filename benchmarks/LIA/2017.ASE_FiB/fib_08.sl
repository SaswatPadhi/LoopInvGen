(set-logic LIA)

(synth-inv inv_fun ((x Int) (y Int)))

(define-fun pre_fun ((x Int) (y Int)) Bool
    (and (= x 0) (= y 0)))
(define-fun trans_fun ((x Int) (y Int) (x! Int) (y! Int)) Bool
    (or (and (= x! (+ x 1)) (= y! (+ y 100))) (and (>= x 4) (= x! (+ x 1)) (= y! (+ y 1))) (and (< x 0) (= x! x) (= y! (- y 1))) (and (= x! x) (= y! y))))
(define-fun post_fun ((x Int) (y Int)) Bool
    (or (< x 4) (> y 2)))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

