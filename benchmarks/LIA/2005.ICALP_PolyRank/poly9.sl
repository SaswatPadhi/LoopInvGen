(set-logic LIA)

(synth-inv inv_fun ((c Int) (y1 Int) (y2 Int) (y1i Int) (y2i Int)))

(define-fun pre_fun ((c Int) (y1 Int) (y2 Int) (y1i Int) (y2i Int)) Bool
    (and (= c 0) (>= y2 1) (>= y1 1) (= y1 y1i) (= y2 y2i)))
(define-fun trans_fun ((c Int) (y1 Int) (y2 Int) (y1i Int) (y2i Int) (c! Int) (y1! Int) (y2! Int) (y1i! Int) (y2i! Int)) Bool
    (and (= y1i! y1i) (= y2i! y2i) (or (and (= y1 y2) (= c! c) (= y1! y1) (= y2! y2)) (and (>= y1 (+ y2 1)) (= c! (+ c 1)) (= y1! (- y1 y2)) (= y2! y2)) (and (>= y2 (+ y1 1)) (= c! (+ c 1)) (= y2! (- y2 y1)) (= y1! y1)))))
(define-fun post_fun ((c Int) (y1 Int) (y2 Int) (y1i Int) (y2i Int)) Bool
    (=> (not (= y1 y2)) (<= c (- (+ y1i y2i) 2))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

