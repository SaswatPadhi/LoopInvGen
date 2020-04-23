(set-logic LIA)

(synth-inv InvF ((x Int) (y Int)))

(define-fun PreF ((x Int) (y Int)) Bool
    (and (= x 1) (= y 0)))
(define-fun TransF ((x Int) (y Int) (x! Int) (y! Int)) Bool
    (and (< y 1024) (= x! 0) (= y! (+ y 1))))
(define-fun PostF ((x Int) (y Int)) Bool
    (or (< y 1024) (not (= x 1))))

(inv-constraint InvF PreF TransF PostF)

(check-synth)

