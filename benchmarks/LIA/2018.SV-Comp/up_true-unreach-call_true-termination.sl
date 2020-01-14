(set-logic LIA)

(synth-inv InvF ((n Int) (i Int) (k Int) (j Int)))

(define-fun PreF ((n Int) (i Int) (k Int) (j Int)) Bool
    (and (= i 0) (= k 0) (= j 0)))
(define-fun TransF ((n Int) (i Int) (k Int) (j Int) (n! Int) (i! Int) (k! Int) (j! Int)) Bool
    (or (and (< i n) (= i! (+ i 1)) (= k! (+ k 1)) (= n! n) (= j! j)) (and (>= i n) (< j n) (= j! (+ j 1)) (= k! (- k 1)) (= n! n) (= i! i))))
(define-fun PostF ((n Int) (i Int) (k Int) (j Int)) Bool
    (or (not (and (>= i n) (< j n))) (> k 0)))

(inv-constraint InvF PreF TransF PostF)

(check-synth)

