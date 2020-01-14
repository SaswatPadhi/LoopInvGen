(set-logic LIA)

(synth-inv inv_fun ((i Int) (c Int) (n Int)))

(define-fun pre_fun ((i Int) (c Int) (n Int)) Bool
    (and (= i 0) (= c 0) (> n 0)))
(define-fun trans_fun ((i Int) (c Int) (n Int) (i! Int) (c! Int) (n! Int)) Bool
    (or (and (>= i n) (= i! i) (= c! c) (= n! n)) (and (< i n) (= i! (+ i 1)) (= c! (+ c i)) (= n! n))))
(define-fun post_fun ((i Int) (c Int) (n Int)) Bool
    (=> (>= i n) (>= c 0)))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

