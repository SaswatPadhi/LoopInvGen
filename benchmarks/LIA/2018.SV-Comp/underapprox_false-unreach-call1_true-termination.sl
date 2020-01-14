(set-logic LIA)

(synth-inv InvF ((x Int) (y Int)))

(define-fun PreF ((x Int) (y Int)) Bool
    (and (= x 0) (= y 1)))
(define-fun TransF ((x Int) (y Int) (x! Int) (y! Int)) Bool
    (and (< x 6) (and (= x! (+ x 1)) (= y! (* y 2)))))
(define-fun PostF ((x Int) (y Int)) Bool
    (or (< x 6) (not (= y 64))))

(inv-constraint InvF PreF TransF PostF)

(check-synth)

