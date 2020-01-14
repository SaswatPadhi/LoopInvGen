(set-logic LIA)

(synth-inv InvF ((i Int) (x Int) (y Int) (n Int)))

(define-fun PreF ((i Int) (x Int) (y Int) (n Int)) Bool
    (and (= i 0) (= x 0) (= y 0) (> n 0)))
(define-fun TransF ((i Int) (x Int) (y Int) (n Int) (i! Int) (x! Int) (y! Int) (n! Int)) Bool
    (and (= i! (+ i 1)) (= x! x) (= y! y) (= n! n)))
(define-fun PostF ((i Int) (x Int) (y Int) (n Int)) Bool
    (= x 0))

(inv-constraint InvF PreF TransF PostF)

(check-synth)

