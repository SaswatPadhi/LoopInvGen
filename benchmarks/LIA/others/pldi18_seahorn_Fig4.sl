(set-logic LIA)

(synth-inv inv_fun ((x Int) (y Int) (i Int) (n Int)))

(define-fun pre_fun ((x Int) (y Int) (i Int) (n Int)) Bool
    (and (= x 0) (= y 0) (= i 0)))
(define-fun trans_fun ((x Int) (y Int) (i Int) (n Int) (x! Int) (y! Int) (i! Int) (n! Int)) Bool
    (and (< i n) (= i! (+ i 1)) (= x! (+ x 1)) (= n! n) (or (and (exists ((k Int)) (= i (* 2 k))) (= y! (+ y 1))) (and (exists ((k Int)) (= i (+ 1 (* 2 k)))) (= y! y)))))
(define-fun post_fun ((x Int) (y Int) (i Int) (n Int)) Bool
    (or (< i n) (or (exists ((k Int)) (= i (+ 1 (* 2 k)))) (= x (* 2 y)))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

