(set-logic LIA)

(synth-inv InvF ((i Int) (n Int) (a Int) (b Int)))

(define-fun PreF ((i Int) (n Int) (a Int) (b Int)) Bool
    (and (= i 0) (= a 0) (= b 0) (>= n 0)))
(define-fun TransF ((i Int) (n Int) (a Int) (b Int) (i! Int) (n! Int) (a! Int) (b! Int)) Bool
    (and (< i n) (or (and (= a! (+ a 1)) (= b! (+ b 2))) (and (= a! (+ a 2)) (= b! (+ b 1)))) (= i! (+ i 1)) (= n! n)))
(define-fun PostF ((i Int) (n Int) (a Int) (b Int)) Bool
    (or (< i n) (= (+ a b) (* 3 n))))

(inv-constraint InvF PreF TransF PostF)

(check-synth)

