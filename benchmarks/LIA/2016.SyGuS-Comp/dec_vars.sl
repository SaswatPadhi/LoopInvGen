(set-logic LIA)

(synth-inv inv_fun ((x Int) (n Int) (v1 Int) (v2 Int) (v3 Int)))

(define-fun pre_fun ((x Int) (n Int) (v1 Int) (v2 Int) (v3 Int)) Bool
    (= x n))
(define-fun trans_fun ((x Int) (n Int) (v1 Int) (v2 Int) (v3 Int) (x! Int) (n! Int) (v1! Int) (v2! Int) (v3! Int)) Bool
    (and (and (> x 0) (= x! (- x 1))) (= n! n)))
(define-fun post_fun ((x Int) (n Int) (v1 Int) (v2 Int) (v3 Int)) Bool
    (not (and (<= x 0) (and (not (= x 0)) (>= n 0)))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

