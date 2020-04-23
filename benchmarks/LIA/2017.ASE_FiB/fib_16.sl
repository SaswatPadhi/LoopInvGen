(set-logic LIA)

(synth-inv inv_fun ((x Int) (y Int) (i Int) (j Int)))

(define-fun pre_fun ((x Int) (y Int) (i Int) (j Int)) Bool
    (and (= x i) (= y j)))
(define-fun trans_fun ((x Int) (y Int) (i Int) (j Int) (x! Int) (y! Int) (i! Int) (j! Int)) Bool
    (or (and (not (= x 0)) (= x! (- x 1)) (= y! (- y 1)) (= i! i) (= j! j)) (and (= x 0) (= x! x) (= y! y) (= i! i) (= j! j))))
(define-fun post_fun ((x Int) (y Int) (i Int) (j Int)) Bool
    (=> (= x 0) (or (not (= i j)) (= y 0))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

