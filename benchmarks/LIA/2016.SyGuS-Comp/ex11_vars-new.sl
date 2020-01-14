(set-logic LIA)

(synth-inv inv_fun ((c Int) (n Int) (v1 Int) (v2 Int) (v3 Int)))

(define-fun pre_fun ((c Int) (n Int) (v1 Int) (v2 Int) (v3 Int)) Bool
    (and (= c 0) (> n 0)))
(define-fun trans_fun ((c Int) (n Int) (v1 Int) (v2 Int) (v3 Int) (c! Int) (n! Int) (v1! Int) (v2! Int) (v3! Int)) Bool
    (or (and (> c n) (= c! (+ c 1))) (and (= c n) (= c! 1))))
(define-fun post_fun ((c Int) (n Int) (v1 Int) (v2 Int) (v3 Int)) Bool
    (not (or (and (not (= c n)) (or (< c 0) (> c n))) (and (= c n) (> n (- 1))))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

