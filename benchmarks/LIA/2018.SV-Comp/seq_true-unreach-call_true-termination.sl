(set-logic LIA)

(synth-inv InvF ((n0 Int) (n1 Int) (i0 Int) (k Int) (i1 Int) (j1 Int)))

(define-fun PreF ((n0 Int) (n1 Int) (i0 Int) (k Int) (i1 Int) (j1 Int)) Bool
    (and (<= (- 0 1000000) n0) (< n0 1000000) (<= (- 0 1000000) n1) (< n1 1000000) (= i1 0) (= j1 0) (= i0 0) (= k 0)))
(define-fun TransF ((n0 Int) (n1 Int) (i0 Int) (k Int) (i1 Int) (j1 Int) (n0! Int) (n1! Int) (i0! Int) (k! Int) (i1! Int) (j1! Int)) Bool
    (or (and (< i0 n0) (= i0! (+ i0 1)) (= k! (+ k 1)) (= n0! n0) (= n1! n1) (= i1! i1) (= j1! j1)) (and (>= i0 n0) (< i1 n1) (= i1! (+ i1 1)) (= k! (+ k 1)) (= n0! n0) (= n1! n1) (= i0! i0) (= j1! j1)) (and (>= i0 n0) (>= i1 n1) (< j1 (+ n0 n1)) (= j1! (+ j1 1)) (= k! (- k 1)) (= n0! n0) (= n1! n1) (= i0! i0) (= i1! i1))))
(define-fun PostF ((n0 Int) (n1 Int) (i0 Int) (k Int) (i1 Int) (j1 Int)) Bool
    (or (not (and (>= i0 n0) (>= i1 n1) (< j1 (+ n0 n1)))) (> k 0)))

(inv-constraint InvF PreF TransF PostF)

(check-synth)

