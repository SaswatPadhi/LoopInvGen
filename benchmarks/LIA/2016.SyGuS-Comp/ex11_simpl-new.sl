(set-logic LIA)

(synth-inv inv_fun ((c Int) (n Int)))

(define-fun pre_fun ((c Int) (n Int)) Bool
    (and (= c 0) (> n 0)))
(define-fun trans_fun ((c Int) (n Int) (c! Int) (n! Int)) Bool
    (or (and (and (> c n) (= c! (+ c 1))) (= n! n)) (and (and (= c n) (= c! 1)) (= n! n))))
(define-fun post_fun ((c Int) (n Int)) Bool
    (and (or (= c n) (and (>= c 0) (<= c n))) (or (not (= c n)) (> n (- 1)))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

