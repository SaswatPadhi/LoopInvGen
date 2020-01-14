(set-logic LIA)

(synth-inv inv_fun ((x Int) (n Int) (m Int) (z1 Int) (z2 Int) (z3 Int)))

(define-fun pre_fun ((x Int) (n Int) (m Int) (z1 Int) (z2 Int) (z3 Int)) Bool
    (and (= x 0) (= m 0)))
(define-fun trans_fun ((x Int) (n Int) (m Int) (z1 Int) (z2 Int) (z3 Int) (x! Int) (n! Int) (m! Int) (z1! Int) (z2! Int) (z3! Int)) Bool
    (or (and (and (and (< x n) (= x! (+ x 1))) (= n! n)) (= m! m)) (and (and (and (< x n) (= x! (+ x 1))) (= n! n)) (= m! x))))
(define-fun post_fun ((x Int) (n Int) (m Int) (z1 Int) (z2 Int) (z3 Int)) Bool
    (not (and (and (>= x n) (> n 0)) (or (<= n m) (< m 0)))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

