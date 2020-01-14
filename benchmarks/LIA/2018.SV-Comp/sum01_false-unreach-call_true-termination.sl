(set-logic LIA)

(synth-inv InvF ((i Int) (n Int) (sn Int)))

(define-fun PreF ((i Int) (n Int) (sn Int)) Bool
    (and (= i 1) (= sn 0) (>= n 0)))
(define-fun TransF ((i Int) (n Int) (sn Int) (i! Int) (n! Int) (sn! Int)) Bool
    (and (<= i n) (ite (< i 10) (= sn! (+ sn 2)) (= sn! sn)) (= i! (+ i 1)) (= n! n)))
(define-fun PostF ((i Int) (n Int) (sn Int)) Bool
    (or (<= i n) (or (= sn (* n 2)) (= sn 0))))

(inv-constraint InvF PreF TransF PostF)

(check-synth)

