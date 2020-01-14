(set-logic LIA)

(synth-inv InvF ((i Int)))

(define-fun PreF ((i Int)) Bool
    (= i 0))
(define-fun TransF ((i Int) (i! Int)) Bool
    (and (< i 1000000) (= i! (+ i 2))))
(define-fun PostF ((i Int)) Bool
    (or (< i 1000000) (= i 1000000)))

(inv-constraint InvF PreF TransF PostF)

(check-synth)

