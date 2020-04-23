(set-logic LIA)

(synth-inv inv_fun ((x Int) (y Int) (failed Bool)))

(define-fun pre_fun ((x Int) (y Int) (failed Bool)) Bool
    (and (= x 0) (= failed false)))
(define-fun trans_fun ((x Int) (y Int) (failed Bool) (x! Int) (y! Int) (failed! Bool)) Bool
    (and (not (= y 0)) (or (and (< y 0) (= x! (- x 1)) (= y! (+ y 1))) (and (>= y 0) (= x! (+ x 1)) (= y! (- y 1)))) (or (and (= x! 0) (= failed! true)) (and (not (= x! 0)) (= failed! failed)))))
(define-fun post_fun ((x Int) (y Int) (failed Bool)) Bool
    (or (not (= y 0)) (= failed false)))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

