(set-logic LIA)

(synth-inv inv_fun ((x Int) (y Int)))

(define-fun pre_fun ((x Int) (y Int)) Bool
    (= x 1))
(define-fun trans_fun ((x Int) (y Int) (x! Int) (y! Int)) Bool
    (and (and (<= x 10) (= y! (- 10 x))) (= x! (+ x 1))))
(define-fun post_fun ((x Int) (y Int)) Bool
    (not (and (and (<= x 10) (= y (- 10 x))) (or (>= y 10) (> 0 y)))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

