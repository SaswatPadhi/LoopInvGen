(set-logic NIA)

(synth-inv inv-f ((x Int) (y Int) (q Int) (r Int)))

(define-fun pre-f ((x Int) (y Int) (q Int) (r Int)) Bool
    (and (> y 0) (>= x 0) (= q 0) (= r x)))
(define-fun trans-f ((x Int) (y Int) (q Int) (r Int) (x! Int) (y! Int) (q! Int) (r! Int)) Bool
    (and (>= r y) (= y! y) (= x! x) (= r! (- r y)) (= q! (+ q 1))))
(define-fun post-f ((x Int) (y Int) (q Int) (r Int)) Bool
    (or (>= r y) (and (= x (+ r (* q y))) (>= r 0))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

