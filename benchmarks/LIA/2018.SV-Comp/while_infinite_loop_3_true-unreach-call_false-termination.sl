(set-logic LIA)

(synth-inv InvF ((x Int)))

(define-fun PreF ((x Int)) Bool
    (= x 0))
(define-fun TransF ((x Int) (x! Int)) Bool
    (= x! 0))
(define-fun PostF ((x Int)) Bool
    (= x 0))

(inv-constraint InvF PreF TransF PostF)

(check-synth)

