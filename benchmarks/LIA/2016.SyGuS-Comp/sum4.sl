(set-logic LIA)

(synth-inv inv_fun ((i Int) (sn Int)))

(define-fun pre_fun ((i Int) (sn Int)) Bool
    (and (= sn 0) (= i 1)))
(define-fun trans_fun ((i Int) (sn Int) (i! Int) (sn! Int)) Bool
    (and (= i! (+ i 1)) (and (<= i 8) (= sn! (+ sn 1)))))
(define-fun post_fun ((i Int) (sn Int)) Bool
    (or (<= i 8) (or (= sn 8) (= sn 0))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

