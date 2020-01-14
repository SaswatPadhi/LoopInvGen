(set-logic LIA)

(synth-inv inv-f ((x Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)))

(define-fun pre-f ((x Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)) Bool
    (and (= x x_1) (= x_1 0)))
(define-fun trans-f ((x Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (x! Int) (x_0! Int) (x_1! Int) (x_2! Int) (x_3! Int)) Bool
    (or (and (= x_2 x) (= x_2 x!)) (and (= x_2 x) (< x_2 100) (= x_3 (+ x_2 1)) (= x_3 x!))))
(define-fun post-f ((x Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)) Bool
    (or (not (= x x_2)) (not (and (not (< x_2 100)) (not (= x_2 100))))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

