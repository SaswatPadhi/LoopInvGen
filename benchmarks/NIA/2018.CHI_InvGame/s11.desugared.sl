(set-logic NIA)

(synth-inv inv-f ((i Int) (j Int) (k Int) (l Int)))

(define-fun pre-f ((i Int) (j Int) (k Int) (l Int)) Bool
    (and (= j 0) (= i l)))
(define-fun trans-f ((i Int) (j Int) (k Int) (l Int) (i! Int) (j! Int) (k! Int) (l! Int)) Bool
    (and (< j 1000) (= i! (+ i k)) (= j! (+ j 1)) (= k! k) (= l! l)))
(define-fun post-f ((i Int) (j Int) (k Int) (l Int)) Bool
    (or (< j 1000) (= i (+ l (* k j)))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

