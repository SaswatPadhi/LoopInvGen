(set-logic LIA)

(synth-inv InvF ((x Int) (y Int)))

(define-fun PreF ((x Int) (y Int)) Bool
    (= y (+ x 1)))
(define-fun TransF ((x Int) (y Int) (x! Int) (y! Int)) Bool
    (and (< x 1024) (= x! (+ x 1)) (= y! (+ y 1))))
(define-fun PostF ((x Int) (y Int)) Bool
    (or (< x 1024) (not (= x y))))

(inv-constraint InvF PreF TransF PostF)

(check-synth)

