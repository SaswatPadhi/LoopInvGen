(set-logic NIA)

(synth-inv inv-f ((n Int) (a Int) (su Int) (t Int)))

(define-fun pre-f ((n Int) (a Int) (su Int) (t Int)) Bool
    (and (= a 0) (= su 1) (= t 1) (> n 0)))
(define-fun trans-f ((n Int) (a Int) (su Int) (t Int) (n! Int) (a! Int) (su! Int) (t! Int)) Bool
    (and (<= su n) (= n! n) (= a! (+ a 1)) (= t! (+ t 2)) (= su! (+ su t!))))
(define-fun post-f ((n Int) (a Int) (su Int) (t Int)) Bool
    (or (<= su n) (= su (* (+ a 1) (+ a 1)))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

