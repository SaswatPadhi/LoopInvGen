(set-logic LIA)

(synth-inv InvF ((i Int) (j Int) (n Int) (sn Int)))

(define-fun PreF ((i Int) (j Int) (n Int) (sn Int)) Bool
    (and (= j 10) (= i 1) (= sn 0) (>= n 0)))
(define-fun TransF ((i Int) (j Int) (n Int) (sn Int) (i! Int) (j! Int) (n! Int) (sn! Int)) Bool
    (and (<= i n) (ite (< i j) (= sn! (+ sn 2)) (= sn! sn)) (= j! (- j 1)) (= i! (+ i 1)) (= n! n)))
(define-fun PostF ((i Int) (j Int) (n Int) (sn Int)) Bool
    (or (<= i n) (or (= sn (* n 2)) (= sn 0))))

(inv-constraint InvF PreF TransF PostF)

(check-synth)

