(set-logic LIA)

(synth-inv InvF ((x Int)))

(define-fun PreF ((x Int)) Bool
    (>= x 0))
(define-fun TransF ((x Int) (x! Int)) Bool
    (and (< x 268435455) (= x! (+ x 1))))
(define-fun PostF ((x Int)) Bool
    (or (< x 268435455) (> x 268435455)))

(inv-constraint InvF PreF TransF PostF)

(check-synth)

