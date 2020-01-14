(set-logic LIA)

(synth-inv inv_fun ((i Int) (j Int) (x Int) (y Int) (z1 Int) (z2 Int) (z3 Int)))

(define-fun pre_fun ((i Int) (j Int) (x Int) (y Int) (z1 Int) (z2 Int) (z3 Int)) Bool
    (and (= i x) (= j y)))
(define-fun trans_fun ((i Int) (j Int) (x Int) (y Int) (z1 Int) (z2 Int) (z3 Int) (i! Int) (j! Int) (x! Int) (y! Int) (z1! Int) (z2! Int) (z3! Int)) Bool
    (and (= i! i) (and (= j! j) (and (not (= x 0)) (and (= x! (- x 1)) (= y! (- y 1)))))))
(define-fun post_fun ((i Int) (j Int) (x Int) (y Int) (z1 Int) (z2 Int) (z3 Int)) Bool
    (or (not (= x 0)) (or (not (= i j)) (= y 0))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

