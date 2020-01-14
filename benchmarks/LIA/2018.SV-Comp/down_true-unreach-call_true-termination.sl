(set-logic LIA)

(synth-inv InvF ((i Int) (k Int) (n Int) (j Int)))

(define-fun PreF ((i Int) (k Int) (n Int) (j Int)) Bool
    (and (= k 0) (= i 0) (= j n)))
(define-fun TransF ((i Int) (k Int) (n Int) (j Int) (i! Int) (k! Int) (n! Int) (j! Int)) Bool
    (or (and (< i n) (= i! (+ i 1)) (= k! (+ k 1)) (= n! n) (= j! j)) (and (>= i n) (> j 0) (= j! (- j 1)) (= k! (- k 1))) (= n! n) (= i! i)))
(define-fun PostF ((i Int) (k Int) (n Int) (j Int)) Bool
    (or (not (and (>= i n) (> j 0))) (> k 0)))

(inv-constraint InvF PreF TransF PostF)

(check-synth)

