(set-logic LIA)

(synth-inv inv_fun ((x Int) (y Int)))

(define-fun pre_fun ((x Int) (y Int)) Bool
    (and (= x 0) (= y 0)))
(define-fun trans_fun ((x Int) (y Int) (x! Int) (y! Int)) Bool
    (and (= x! x) (and (<= 0 y) (= y! (+ x y)))))
(define-fun post_fun ((x Int) (y Int)) Bool
    (>= y 0))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

