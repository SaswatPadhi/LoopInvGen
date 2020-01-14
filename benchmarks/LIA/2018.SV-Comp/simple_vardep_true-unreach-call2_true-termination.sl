(set-logic LIA)

(synth-inv InvF ((i Int) (j Int) (k Int)))

(define-fun PreF ((i Int) (j Int) (k Int)) Bool
    (and (= i 0) (= j 0) (= k 0)))
(define-fun TransF ((i Int) (j Int) (k Int) (i! Int) (j! Int) (k! Int)) Bool
    (and (< k 268435455) (= i! (+ i 1)) (= j! (+ j 2)) (= k! (+ k 3))))
(define-fun PostF ((i Int) (j Int) (k Int)) Bool
    (or (< k 268435455) (and (= k (* 3 i)) (= j (* 2 i)))))

(inv-constraint InvF PreF TransF PostF)

(check-synth)

