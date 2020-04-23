(set-logic LIA)

(synth-inv inv_fun ((x Int) (y Int) (z1 Int) (z2 Int) (z3 Int)))

(define-fun pre_fun ((x Int) (y Int) (z1 Int) (z2 Int) (z3 Int)) Bool
    (= x 1))
(define-fun trans_fun ((x Int) (y Int) (z1 Int) (z2 Int) (z3 Int) (x! Int) (y! Int) (z1! Int) (z2! Int) (z3! Int)) Bool
    (and (< x y) (= x! (+ x x))))
(define-fun post_fun ((x Int) (y Int) (z1 Int) (z2 Int) (z3 Int)) Bool
    (or (not (>= x y)) (>= x 1)))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

