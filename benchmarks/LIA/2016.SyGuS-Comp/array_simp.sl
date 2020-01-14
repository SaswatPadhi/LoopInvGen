(set-logic LIA)

(synth-inv inv_fun ((x Int) (y Int) (z Int) (size Int)))

(define-fun pre_fun ((x Int) (y Int) (z Int) (size Int)) Bool
    (= x 0))
(define-fun trans_fun ((x Int) (y Int) (z Int) (size Int) (x! Int) (y! Int) (z! Int) (size! Int)) Bool
    (or (and (= x! (+ x 1)) (and (= y! z!) (and (<= z! y) (< x size)))) (and (= x! (+ x 1)) (and (= y! y) (and (> z! y) (< x size))))))
(define-fun post_fun ((x Int) (y Int) (z Int) (size Int)) Bool
    (not (and (and (>= x size) (< z y)) (> size 0))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

