(set-logic NIA)

(synth-inv inv-f ((n Int) (x Int) (y Int) (z Int)))

(define-fun pre-f ((n Int) (x Int) (y Int) (z Int)) Bool
    (and (= n 0) (= x 0) (= y 1) (= z 6)))
(define-fun trans-f ((n Int) (x Int) (y Int) (z Int) (n! Int) (x! Int) (y! Int) (z! Int)) Bool
    (and (< n 100) (= n! (+ n 1)) (= x! (+ x y)) (= y! (+ y z)) (= z! (+ z 6))))
(define-fun post-f ((n Int) (x Int) (y Int) (z Int)) Bool
    (or (< n 100) (= x (* n (* n n)))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

