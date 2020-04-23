(set-logic LIA)

(synth-inv inv_fun ((k Int) (b Int) (i Int) (j Int) (n Int)))

(define-fun pre_fun ((k Int) (b Int) (i Int) (j Int) (n Int)) Bool
    (and (> k 0) (= i j) (= n 0) (or (= b 1) (= b 0))))
(define-fun trans_fun ((k Int) (b Int) (i Int) (j Int) (n Int) (k! Int) (b! Int) (i! Int) (j! Int) (n! Int)) Bool
    (or (and (>= n (* 2 k)) (= k! k) (= b! b) (= i! i) (= j! j) (= n! n)) (and (< n (* 2 k)) (= b 1) (= k! k) (= b! 0) (= i! (+ i 1)) (= j! j) (= n! (+ n 1))) (and (< n (* 2 k)) (not (= b 1)) (= k! k) (= b! 1) (= i! i) (= j! (+ j 1)) (= n! (+ n 1)))))
(define-fun post_fun ((k Int) (b Int) (i Int) (j Int) (n Int)) Bool
    (=> (>= n (* 2 k)) (= i j)))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

