(set-logic LIA)

(synth-inv inv_fun ((n Int) (m Int) (x Int) (y Int)))

(define-fun pre_fun ((n Int) (m Int) (x Int) (y Int)) Bool
    (and (>= n 0) (>= m 0) (< m n) (= x 0) (= y m)))
(define-fun trans_fun ((n Int) (m Int) (x Int) (y Int) (n! Int) (m! Int) (x! Int) (y! Int)) Bool
    (or (and (< x n) (<= (+ x 1) m) (= x! (+ x 1)) (= y! y) (= n! n) (= m! m)) (and (< x n) (> (+ x 1) m) (= x! (+ x 1)) (= y! (+ y 1)) (= n! n) (= m! m)) (and (>= x n) (= x! x) (= y! y) (= n! n) (= m! m))))
(define-fun post_fun ((n Int) (m Int) (x Int) (y Int)) Bool
    (=> (not (< x n)) (= y n)))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

