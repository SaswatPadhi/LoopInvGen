(set-logic LIA)

(synth-inv InvF ((n Int) (x Int) (y Int)))

(define-fun PreF ((n Int) (x Int) (y Int)) Bool
    (and (= y 0) (= x n)))
(define-fun TransF ((n Int) (x Int) (y Int) (n! Int) (x! Int) (y! Int)) Bool
    (and (> x 0) (= x! (- x 1)) (= y! (+ y 1)) (= n! n)))
(define-fun PostF ((n Int) (x Int) (y Int)) Bool
    (or (> x 0) (= y n)))

(inv-constraint InvF PreF TransF PostF)

(check-synth)

