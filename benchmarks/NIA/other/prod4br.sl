(set-logic NIA)

(synth-inv inv-f ((x Int) (y Int) (a Int) (b Int) (p Int) (q Int)))

(define-fun pre-f ((x Int) (y Int) (a Int) (b Int) (p Int) (q Int)) Bool
    (and (>= x 0) (>= y 0) (= a x) (= b y) (= p 1) (= q 0)))
(define-fun trans-f ((x Int) (y Int) (a Int) (b Int) (p Int) (q Int) (x! Int) (y! Int) (a! Int) (b! Int) (p! Int) (q! Int)) Bool
    (and (not (= a 0)) (not (= b 0)) (= x! x) (= y! y) (or (and (= (mod a 2) 0) (= (mod b 2) 0) (= q! q) (= a! (div a 2)) (= b! (div b 2)) (= p! (* 4 p))) (and (= (mod a 2) 1) (= (mod b 2) 0) (= p! p) (= b! b) (= a! (- a 1)) (= q! (+ q (* b p)))) (and (= (mod a 2) 0) (= (mod b 2) 1) (= p! p) (= a! a) (= b! (- b 1)) (= q! (+ q (* a p)))) (and (= (mod a 2) 1) (= (mod b 2) 1) (= p! p) (= b! (- b 1)) (= a! (- a 1)) (= q! (+ q (* p (+ (+ a! b!) (- 0 1)))))))))
(define-fun post-f ((x Int) (y Int) (a Int) (b Int) (p Int) (q Int)) Bool
    (or (and (not (= a 0)) (not (= b 0))) (= q (* x y))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

