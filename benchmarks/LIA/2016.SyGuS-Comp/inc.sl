(set-logic LIA)

(synth-inv inv_fun ((x Int)))

(define-fun pre_fun ((x Int)) Bool
    (= x 0))
(define-fun trans_fun ((x Int) (x! Int)) Bool
    (and (< x 100) (= x! (+ x 1))))
(define-fun post_fun ((x Int)) Bool
    (or (not (>= x 100)) (= x 100)))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

