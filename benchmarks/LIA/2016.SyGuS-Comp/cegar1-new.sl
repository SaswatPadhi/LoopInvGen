(set-logic LIA)

(synth-inv inv_fun ((x Int) (y Int)))

(define-fun pre_fun ((x Int) (y Int)) Bool
    (and (and (>= x 0) (and (<= x 10) (<= y 10))) (>= y 0)))
(define-fun trans_fun ((x Int) (y Int) (x! Int) (y! Int)) Bool
    (and (= x! (+ x 10)) (= y! (+ y 10))))
(define-fun post_fun ((x Int) (y Int)) Bool
    (not (and (= x 20) (= y 0))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

