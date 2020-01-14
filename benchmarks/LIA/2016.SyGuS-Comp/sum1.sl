(set-logic LIA)

(synth-inv inv_fun ((i Int) (n Int) (sn Int)))

(define-fun pre_fun ((i Int) (n Int) (sn Int)) Bool
    (and (= sn 0) (= i 1)))
(define-fun trans_fun ((i Int) (n Int) (sn Int) (i! Int) (n! Int) (sn! Int)) Bool
    (and (= n! n) (and (= i! (+ i 1)) (and (<= i n) (= sn! (+ sn 1))))))
(define-fun post_fun ((i Int) (n Int) (sn Int)) Bool
    (or (<= i n) (or (= sn n) (= sn 0))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

