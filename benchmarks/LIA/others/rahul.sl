(set-logic LIA)

(synth-inv inv_fun ((N Int) (x Int) (y Int)))

(define-fun pre_fun ((N Int) (x Int) (y Int)) Bool
    (and (>= N 0) (= x y) (<= x N)))
(define-fun trans_fun ((N Int) (x Int) (y Int) (N! Int) (x! Int) (y! Int)) Bool
    (and (>= y 0) (or (and (<= x N) (= y! (+ y 1))) (and (> x N) (= y! (- y 1)))) (= x! (+ x 1)) (= N! N)))
(define-fun post_fun ((N Int) (x Int) (y Int)) Bool
    (or (>= y 0) (< x (+ 4 (* 2 N)))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

