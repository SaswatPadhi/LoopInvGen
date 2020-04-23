(set-logic LIA)

(synth-inv inv_fun ((x Int) (y Int) (i Int)))

(define-fun pre_fun ((x Int) (y Int) (i Int)) Bool
    (and (and (and (= i 0) (>= x 0)) (>= y 0)) (>= x y)))
(define-fun trans_fun ((x Int) (y Int) (i Int) (x! Int) (y! Int) (i! Int)) Bool
    (and (and (< i y) (= i! (+ i 1))) (and (= y! y) (= x! x))))
(define-fun post_fun ((x Int) (y Int) (i Int)) Bool
    (not (and (< i y) (or (>= i x) (> 0 i)))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

