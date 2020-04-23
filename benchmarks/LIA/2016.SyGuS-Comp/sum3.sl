(set-logic LIA)

(synth-inv inv_fun ((x Int) (sn Int)))

(define-fun pre_fun ((x Int) (sn Int)) Bool
    (and (= sn 0) (= x 0)))
(define-fun trans_fun ((x Int) (sn Int) (x! Int) (sn! Int)) Bool
    (and (= x! (+ x 1)) (= sn! (+ sn 1))))
(define-fun post_fun ((x Int) (sn Int)) Bool
    (or (= sn x) (= sn (- 1))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

