(set-logic NIA)

(synth-inv inv_fun ((c Int) (y1 Int) (y2 Int) (y1i Int) (y2i Int)))

(define-fun pre_fun ((c Int) (y1 Int) (y2 Int) (y1i Int) (y2i Int)) Bool
    (and (= c 0) (>= y2 1) (= y1 y1i) (= y2 y2i)))
(define-fun trans_fun ((c Int) (y1 Int) (y2 Int) (y1i Int) (y2i Int) (c! Int) (y1! Int) (y2! Int) (y1i! Int) (y2i! Int)) Bool
    (and (= y1i! y1i) (= y2i! y2i) (or (and (>= y1 101) (= y2 1) (= c! c) (= y1! y1) (= y2! y2)) (and (>= y1 101) (<= y2 0) (= c! (+ c 1)) (= y1! (- y1 10)) (= y2! (- y2 1))) (and (>= y1 101) (>= y2 2) (= c! (+ c 1)) (= y1! (- y1 10)) (= y2! (- y2 1))) (and (<= y1 100) (= c! (+ c 1)) (= y1! (+ y1 11)) (= y2! (+ y2 1))))))
(define-fun post_fun ((c Int) (y1 Int) (y2 Int) (y1i Int) (y2i Int)) Bool
    (=> (not (and (= y2 1) (>= y1 101))) (<= c (+ (* y2i y2i) (* (+ (- 101 y1i) (* 10 y2i)) (+ (- 101 y1i) (* 10 y2i)))))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

