(set-logic LIA)

(synth-inv inv_fun ((x Int) (z Int)))

(define-fun pre_fun ((x Int) (z Int)) Bool
    (and (> x (- 0 100)) (< x 200) (> z 100) (< z 200)))
(define-fun trans_fun ((x Int) (z Int) (x! Int) (z! Int)) Bool
    (and (< x 100) (> z 100) (or (and (= x! (+ x 1)) (= z! z)) (and (= x! (- x 1)) (= z! (- z 1))))))
(define-fun post_fun ((x Int) (z Int)) Bool
    (or (and (< x 100) (> z 100)) (or (>= x 100) (<= z 100))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

