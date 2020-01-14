(set-logic LIA)

(synth-inv inv_fun ((w Int) (x Int) (y Int) (z Int)))

(define-fun pre_fun ((w Int) (x Int) (y Int) (z Int)) Bool
    (and (= w 0) (= x 0) (= y 0) (= z 0)))
(define-fun trans_fun ((w Int) (x Int) (y Int) (z Int) (w! Int) (x! Int) (y! Int) (z! Int)) Bool
    (and (or (and (= x! (+ x 1)) (= y! (+ y 100))) (and (>= x 4) (= x! (+ x 1)) (= y! (+ y 1))) (and (> y (* 10 w)) (>= z (* 100 x)) (= y! (- 0 y)) (= x! x))) (= w! (+ w 1)) (= z! (+ z 10))))
(define-fun post_fun ((w Int) (x Int) (y Int) (z Int)) Bool
    (not (and (>= x 4) (<= y 2))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

