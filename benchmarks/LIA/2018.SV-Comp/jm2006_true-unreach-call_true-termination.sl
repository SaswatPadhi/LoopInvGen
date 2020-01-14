(set-logic LIA)

(synth-inv inv_fun ((i Int) (j Int) (x Int) (y Int)))

(define-fun pre_fun ((i Int) (j Int) (x Int) (y Int)) Bool
    (and (>= i 0) (>= j 0) (= x i) (= y j)))
(define-fun trans_fun ((i Int) (j Int) (x Int) (y Int) (i! Int) (j! Int) (x! Int) (y! Int)) Bool
    (and (not (= x 0)) (= i! i) (= j! j) (= x! (- x 1)) (= y! (- y 1))))
(define-fun post_fun ((i Int) (j Int) (x Int) (y Int)) Bool
    (or (not (= x 0)) (=> (= i j) (= y 0))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

