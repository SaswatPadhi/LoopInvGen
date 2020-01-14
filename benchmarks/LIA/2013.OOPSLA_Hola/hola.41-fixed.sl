(set-logic LIA)

(synth-inv inv_fun ((i Int) (j Int) (k Int) (n Int)))

(define-fun pre_fun ((i Int) (j Int) (k Int) (n Int)) Bool
    (and (or (= k 1) (>= k 0)) (and (>= n 0) (and (= i 0) (= j 0)))))
(define-fun trans_fun ((i Int) (j Int) (k Int) (n Int) (i! Int) (j! Int) (k! Int) (n! Int)) Bool
    (and (<= i n) (and (= n! n) (and (= k! k) (and (= i! (+ i 1)) (= j! (+ j i!)))))))
(define-fun post_fun ((i Int) (j Int) (k Int) (n Int)) Bool
    (or (<= i n) (> (+ i (+ j k)) (* 2 n))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

