(set-logic LIA)

(synth-inv InvF ((i Int) (j Int) (k Int)))

(define-fun PreF ((i Int) (j Int) (k Int)) Bool
    (and (= i 1) (= j 1) (<= 0 k) (<= k 1)))
(define-fun TransF ((i Int) (j Int) (k Int) (i! Int) (j! Int) (k! Int)) Bool
    (and (< i 1000000) (= i! (+ i 1)) (= j! (+ j k)) (= k! (- k 1))))
(define-fun PostF ((i Int) (j Int) (k Int)) Bool
    (or (not (< i 1000000)) (and (<= 1 (+ i k)) (<= (+ i k) 2) (>= i 1))))

(inv-constraint InvF PreF TransF PostF)

(check-synth)

