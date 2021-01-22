(set-logic LRA)

(synth-inv inv_fun ((x Real) (n Real)))

(define-fun pre_fun ((x Real) (n Real)) Bool
    (= x (* 2. n)))
(define-fun trans_fun ((x Real) (n Real) (x! Real) (n! Real)) Bool
    (and (and (>= x 1.0) (= x! (/ x 2.))) (= n! (/ n 2.))))
(define-fun post_fun ((x Real) (n Real)) Bool
    (and (not (and (<= x 1.) (and (not (= x 1.)) (>= n 0.5)))) (= x (* 2. n))))


(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)