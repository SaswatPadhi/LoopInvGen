(set-logic LIA)

(synth-inv inv_fun ((x Int) (y Int) (k Int) (j Int) (i Int) (n Int) (m Int)))

(define-fun pre_fun ((x Int) (y Int) (k Int) (j Int) (i Int) (n Int) (m Int)) Bool
    (and (= (+ x y) k) (= m 0) (= j 0)))
(define-fun trans_fun ((x Int) (y Int) (k Int) (j Int) (i Int) (n Int) (m Int) (x! Int) (y! Int) (k! Int) (j! Int) (i! Int) (n! Int) (m! Int)) Bool
    (or (and (< j n) (= j i) (= x! (+ x 1)) (= y! (- y 1)) (= k! k) (= j! (+ j 1)) (= i! i) (= n! n) (= m! m)) (and (< j n) (= j i) (= x! (+ x 1)) (= y! (- y 1)) (= k! k) (= j! (+ j 1)) (= i! i) (= n! n) (= m! j)) (and (< j n) (not (= j i)) (= x! (- x 1)) (= y! (+ y 1)) (= k! k) (= j! (+ j 1)) (= i! i) (= n! n) (= m! m)) (and (< j n) (not (= j i)) (= x! (- x 1)) (= y! (+ y 1)) (= k! k) (= j! (+ j 1)) (= i! i) (= n! n) (= m! j)) (and (>= j n) (= x! x) (= y! y) (= k! k) (= j! j) (= i! i) (= n! n) (= m! m))))
(define-fun post_fun ((x Int) (y Int) (k Int) (j Int) (i Int) (n Int) (m Int)) Bool
    (=> (>= j n) (and (= (+ x y) k) (or (<= n 0) (<= 0 m)) (or (<= n 0) (<= m n)))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

