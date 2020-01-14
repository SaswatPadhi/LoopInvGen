(set-logic ALIA)

(synth-inv inv_fun ((x (Array Int Int)) (y Int) (n Int)))

(define-fun pre_fun ((x (Array Int Int)) (y Int) (n Int)) Bool
    (and (>= n 0) (and (= n (select x 0)) (= y 0))))
(define-fun trans_fun ((x (Array Int Int)) (y Int) (n Int) (x! (Array Int Int)) (y! Int) (n! Int)) Bool
    (and (> (select x 0) 0) (and (= n! n) (and (= y! (+ y 1)) (= x! (store x 0 (- (select x 0) 1)))))))
(define-fun post_fun ((x (Array Int Int)) (y Int) (n Int)) Bool
    (or (> (select x 0) 0) (= n (+ (select x 0) y))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

