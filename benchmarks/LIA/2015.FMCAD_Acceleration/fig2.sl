(set-logic LIA)

(synth-inv inv_fun ((x Int) (y Int) (z Int) (w Int)))

(define-fun pre_fun ((x Int) (y Int) (z Int) (w Int)) Bool
    (and (= x 0) (= y 0) (= z 0) (= w 0)))
(define-fun trans_fun ((x Int) (y Int) (z Int) (w Int) (x! Int) (y! Int) (z! Int) (w! Int)) Bool
    (or (and (= x! (+ x 1)) (= y! (+ y 2)) (= z! z) (= w! w)) (and (>= x 4) (= x! (+ x 1)) (= y! (+ y 3)) (= z! (+ z 10)) (= w! (+ w 10))) (and (>= x z) (> w y) (= x! (- 0 x)) (= y! (- 0 y)) (= z! z) (= w! w))))
(define-fun post_fun ((x Int) (y Int) (z Int) (w Int)) Bool
    (>= (* 3 x) y))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

