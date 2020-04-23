(set-logic LIA)

(synth-inv InvF ((i Int) (x Int) (y Int) (n Int)))

(define-fun PreF ((i Int) (x Int) (y Int) (n Int)) Bool
    (and (= i 0) (= x 0) (= y 0) (> n 0)))
(define-fun TransF ((i Int) (x Int) (y Int) (n Int) (i! Int) (x! Int) (y! Int) (n! Int)) Bool
    (and (< i n) (= x! (+ x y!)) (not (= y! 0)) (= i! i) (= n! n)))
(define-fun PostF ((i Int) (x Int) (y Int) (n Int)) Bool
    (or (< i n) (= x 0)))

(inv-constraint InvF PreF TransF PostF)

(check-synth)

