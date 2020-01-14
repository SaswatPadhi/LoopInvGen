(set-logic LIA)

(synth-inv inv_fun ((x1 Int) (x2 Int) (x3 Int) (x4 Int)))

(define-fun pre_fun ((x1 Int) (x2 Int) (x3 Int) (x4 Int)) Bool
    (and (and (= x1 0) (and (= x2 0) (= x3 0))) (= x4 (- 1))))
(define-fun trans_fun ((x1 Int) (x2 Int) (x3 Int) (x4 Int) (x1! Int) (x2! Int) (x3! Int) (x4! Int)) Bool
    (and (<= x1! 0) (and (>= x1! (+ x4! 1)) (and (= x2! x3!) (or (>= x4! 0) (<= x4! x3!))))))
(define-fun post_fun ((x1 Int) (x2 Int) (x3 Int) (x4 Int)) Bool
    (and (<= x1 0) (and (>= x1 (+ x4 1)) (and (= x2 x3) (or (>= x4 0) (<= x4 x3))))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

