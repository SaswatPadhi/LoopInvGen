(set-logic LIA)

(synth-inv inv_fun ((x1 Int) (x2 Int) (x3 Int)))

(define-fun pre_fun ((x1 Int) (x2 Int) (x3 Int)) Bool
    (and (= x1 0) (and (= x2 0) (= x3 0))))
(define-fun trans_fun ((x1 Int) (x2 Int) (x3 Int) (x1! Int) (x2! Int) (x3! Int)) Bool
    (and (<= x1! x2!) (or (>= x2! 0) (<= (- x2! x3!) 2))))
(define-fun post_fun ((x1 Int) (x2 Int) (x3 Int)) Bool
    (and (<= x1 x2) (or (>= x2 0) (<= (- x2 x3) 2))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

