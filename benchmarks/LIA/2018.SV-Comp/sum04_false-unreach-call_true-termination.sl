(set-logic LIA)

(synth-inv InvF ((i Int) (sn Int)))

(define-fun PreF ((i Int) (sn Int)) Bool
    (and (= sn 0) (= i 1)))
(define-fun TransF ((i Int) (sn Int) (i! Int) (sn! Int)) Bool
    (and (<= i 8) (ite (< i 4) (= sn! (+ sn 2)) (= sn! sn)) (= i! (+ i 1))))
(define-fun PostF ((i Int) (sn Int)) Bool
    (or (<= i 8) (or (= sn (* 8 2)) (= sn 0))))

(inv-constraint InvF PreF TransF PostF)

(check-synth)

