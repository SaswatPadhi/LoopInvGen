(set-logic LIA)

(synth-inv inv_fun ((c Int) (i Int) (j Int) (i0 Int) (j0 Int) (an Int) (bn Int)))

(define-fun pre_fun ((c Int) (i Int) (j Int) (i0 Int) (j0 Int) (an Int) (bn Int)) Bool
    (and (= c 0) (= i i0) (= j j0)))
(define-fun trans_fun ((c Int) (i Int) (j Int) (i0 Int) (j0 Int) (an Int) (bn Int) (c! Int) (i! Int) (j! Int) (i0! Int) (j0! Int) (an! Int) (bn! Int)) Bool
    (and (= an! an) (= bn! bn) (= i0! i0) (= j0! j0) (or (and (< an i) (< bn j) (= c! c) (= i! i) (= j! j)) (and (>= an i) (>= bn j) (= c! (+ c 1)) (= i! i) (= j! (+ j 1))) (and (>= an i) (>= bn j) (= c! (+ c 1)) (= i! (+ i 1)) (= j! j)) (and (>= an i) (<= bn j) (= c! (+ c 1)) (= i! (+ i 1)) (= j! j)) (and (<= an i) (>= bn j) (= c! (+ c 1)) (= i! i) (= j! (+ j 1))))))
(define-fun post_fun ((c Int) (i Int) (j Int) (i0 Int) (j0 Int) (an Int) (bn Int)) Bool
    (=> (or (>= an i) (>= bn j)) (or (and (>= an i0) (>= bn j0)) (<= c (+ (- an i0) (- bn j0))) (and (>= an i0) (< bn j0) (<= c (- an i0))) (and (< an i0) (>= bn j0) (<= c (- bn j0))) (and (< an i0) (< bn j0) (= c 0)))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

