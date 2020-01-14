(set-logic LIA)

(synth-inv inv_fun ((c Int)))

(define-fun pre_fun ((c Int)) Bool
    (= c 0))
(define-fun trans_fun ((c Int) (c! Int)) Bool
    (or (and (not (= c 4)) (= c! (+ c 1))) (and (= c 4) (= c! 1))))
(define-fun post_fun ((c Int)) Bool
    (not (and (not (= c 4)) (or (< c 0) (> c 4)))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

