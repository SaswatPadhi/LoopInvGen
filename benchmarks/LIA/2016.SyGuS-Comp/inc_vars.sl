(set-logic LIA)

(synth-inv inv_fun ((x Int) (n Int) (v1 Int) (v2 Int) (v3 Int)))

(define-fun pre_fun ((x Int) (n Int) (v1 Int) (v2 Int) (v3 Int)) Bool
    (= x 0))
(define-fun trans_fun ((x Int) (n Int) (v1 Int) (v2 Int) (v3 Int) (x! Int) (n! Int) (v1! Int) (v2! Int) (v3! Int)) Bool
    (and (= n! n) (and (< x n) (= x! (+ x 1)))))
(define-fun post_fun ((x Int) (n Int) (v1 Int) (v2 Int) (v3 Int)) Bool
    (or (not (>= x n)) (or (= x n) (< n 0))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

