(set-logic NIA)

(synth-inv inv-f ((a Int) (b Int) (x Int) (y Int) (u Int) (v Int)))

(define-fun pre-f ((a Int) (b Int) (x Int) (y Int) (u Int) (v Int)) Bool
    (and (> a 0) (> b 0) (= x a) (= y b) (= u b) (= v a)))
(define-fun trans-f ((a Int) (b Int) (x Int) (y Int) (u Int) (v Int) (a! Int) (b! Int) (x! Int) (y! Int) (u! Int) (v! Int)) Bool
    (and (not (= x y)) (= a! a) (= b! b) (or (and (> x y) (= y! y) (= u! u) (= x! (- x y)) (= v! (+ v u))) (and (not (> x y)) (= x! x) (= v! v) (= y! (- y x)) (= u! (+ u v))))))
(define-fun post-f ((a Int) (b Int) (x Int) (y Int) (u Int) (v Int)) Bool
    (or (not (= x y)) (and (> u 0) (> v 0) (= 0 (mod (+ u v) a)) (= 0 (mod (+ u v) b)))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

