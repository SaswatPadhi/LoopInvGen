(set-logic LIA)

(synth-inv inv_fun ((x Int) (m Int) (n Int)))

(define-fun pre_fun ((x Int) (m Int) (n Int)) Bool
    (and (= x 0) (= m 0)))
(define-fun trans_fun ((x Int) (m Int) (n Int) (x! Int) (m! Int) (n! Int)) Bool
    (and (< x n) (or (= m! x) (= m! m)) (= n! n) (= x! (+ x 1))))
(define-fun post_fun ((x Int) (m Int) (n Int)) Bool
    (and (or (>= m 0) (<= n 0)) (or (< m n) (<= n 0))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

