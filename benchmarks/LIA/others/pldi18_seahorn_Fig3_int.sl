(set-logic LIA)

(synth-inv inv_fun ((x Int) (y Int) (failed Int)))

(define-fun pre_fun ((x Int) (y Int) (failed Int)) Bool
    (and (= x 0) (= failed 0)))
(define-fun trans_fun ((x Int) (y Int) (failed Int) (x! Int) (y! Int) (failed! Int)) Bool
    (and (not (= y 0)) (or (and (< y 0) (= x! (- x 1)) (= y! (+ y 1))) (and (>= y 0) (= x! (+ x 1)) (= y! (- y 1)))) (or (and (= x! 0) (= failed! 1)) (and (not (= x! 0)) (= failed! failed)))))
(define-fun post_fun ((x Int) (y Int) (failed Int)) Bool
    (or (not (= y 0)) (= failed 0)))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

