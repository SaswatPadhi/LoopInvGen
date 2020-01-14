(set-logic NIA)

(synth-inv inv-f ((i Int) (a Int) (c Int)))

(define-fun pre-f ((i Int) (a Int) (c Int)) Bool
    (and (= i 0) (= a 0) (= c 0)))
(define-fun trans-f ((i Int) (a Int) (c Int) (i! Int) (a! Int) (c! Int)) Bool
    (and (< i 10) (= c! (+ c (+ 1 (* 6 a)))) (= a! (+ a (+ i 1))) (= i! (+ i 1))))
(define-fun post-f ((i Int) (a Int) (c Int)) Bool
    (or (< i 10) (= c (* i (* i i)))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

