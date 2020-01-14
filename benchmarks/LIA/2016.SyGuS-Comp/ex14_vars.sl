(set-logic LIA)

(synth-inv inv_fun ((x Int) (y Int) (n Int) (v1 Int) (v2 Int) (v3 Int)))

(define-fun pre_fun ((x Int) (y Int) (n Int) (v1 Int) (v2 Int) (v3 Int)) Bool
    (= x 1))
(define-fun trans_fun ((x Int) (y Int) (n Int) (v1 Int) (v2 Int) (v3 Int) (x! Int) (y! Int) (n! Int) (v1! Int) (v2! Int) (v3! Int)) Bool
    (and (and (<= x n) (= y! (- n x))) (= x! (+ x 1))))
(define-fun post_fun ((x Int) (y Int) (n Int) (v1 Int) (v2 Int) (v3 Int)) Bool
    (not (and (and (<= x n) (= y (- n x))) (or (>= y n) (> 0 y)))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

