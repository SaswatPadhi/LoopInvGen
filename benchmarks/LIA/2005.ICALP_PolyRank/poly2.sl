(set-logic LIA)

(synth-inv inv_fun ((c Int) (x Int) (y Int) (x0 Int) (y0 Int)))

(define-fun pre_fun ((c Int) (x Int) (y Int) (x0 Int) (y0 Int)) Bool
    (and (= c 0) (= x x0) (= y y0)))
(define-fun trans_fun ((c Int) (x Int) (y Int) (x0 Int) (y0 Int) (c! Int) (x! Int) (y! Int) (x0! Int) (y0! Int)) Bool
    (and (= x0! x0) (= y0! y0) (or (and (< x y) (= c! c) (= x! x) (= y! y)) (and (>= x y) (= c! (+ c 1)) (<= x! (- x 1)) (= y! y)) (and (>= x y) (= c! (+ c 1)) (>= y! (+ y 1)) (= x! x)))))
(define-fun post_fun ((c Int) (x Int) (y Int) (x0 Int) (y0 Int)) Bool
    (=> (>= x y) (ite (>= x0 y0) (<= c (- x0 y0)) (= c 0))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

