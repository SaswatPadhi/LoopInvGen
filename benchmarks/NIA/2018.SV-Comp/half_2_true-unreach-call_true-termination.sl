(set-logic NIA)

(synth-inv InvF ((n Int) (i Int) (k Int) (j Int)))

(define-fun PreF ((n Int) (i Int) (k Int) (j Int)) Bool
    (and (<= n 1000000) (= k n) (= i 0) (= j 0)))
(define-fun TransF ((n Int) (i Int) (k Int) (j Int) (n! Int) (i! Int) (k! Int) (j! Int)) Bool
    (or (and (< i n) (= k! (- k 1)) (= i! (+ i 2)) (= n! n) (= j! j)) (and (>= i n) (< j (div n 2)) (= k! (- k 1)) (= j! (+ j 1)) (= i! i) (= n! n))))
(define-fun PostF ((n Int) (i Int) (k Int) (j Int)) Bool
    (or (not (and (>= i n) (< j (div n 2)))) (> k 0)))

(inv-constraint InvF PreF TransF PostF)

(check-synth)

