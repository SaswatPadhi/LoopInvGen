(set-logic LIA)

(synth-inv inv_fun ((x Int) (m Int) (n Int)))

(define-fun pre_fun ((x Int) (m Int) (n Int)) Bool
    (and (= x 0) (= m 0) (> n 0)))
(define-fun trans_fun ((x Int) (m Int) (n Int) (x! Int) (m! Int) (n! Int)) Bool
    (or (and (>= x n) (= x! x) (= m! m) (= n! n)) (and (< x n) (= x! (+ x 1)) (= m! x) (= n! n)) (and (< x n) (= x! (+ x 1)) (= m! m) (= n! n))))
(define-fun post_fun ((x Int) (m Int) (n Int)) Bool
    (=> (>= x n) (or (<= n 0) (and (<= 0 m) (< m n)))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

