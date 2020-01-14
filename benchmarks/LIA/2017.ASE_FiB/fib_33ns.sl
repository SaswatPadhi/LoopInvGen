(set-logic LIA)

(synth-inv inv_fun ((x Int) (y Int) (z Int) (c Int) (k Int) (turn Int)))

(define-fun pre_fun ((x Int) (y Int) (z Int) (c Int) (k Int) (turn Int)) Bool
    (and (= z k) (= x 0) (= y 0) (= turn 0)))
(define-fun trans_fun ((x Int) (y Int) (z Int) (c Int) (k Int) (turn Int) (x! Int) (y! Int) (z! Int) (c! Int) (k! Int) (turn! Int)) Bool
    (or (and (= turn 0) (= x! x) (= y! y) (= z! z) (= c! 0) (= k! k) (= turn! 1)) (and (= turn 0) (= x! x) (= y! y) (= z! z) (= c! 0) (= k! k) (= turn! 2)) (and (= turn 1) (= z (- (+ k y) c)) (= x! (+ x 1)) (= y! (+ y 1)) (= z! z) (= c! (+ c 1)) (= k! k) (= turn! 1)) (and (= turn 1) (not (= z (- (+ k y) c))) (= x! (+ x 1)) (= y! (- y 1)) (= z! z) (= c! (+ c 1)) (= k! k) (= turn! 1)) (and (= turn 1) (= z (- (+ k y) c)) (= x! (+ x 1)) (= y! (+ y 1)) (= z! z) (= c! (+ c 1)) (= k! k) (= turn! 2)) (and (= turn 1) (not (= z (- (+ k y) c))) (= x! (+ x 1)) (= y! (- y 1)) (= z! z) (= c! (+ c 1)) (= k! k) (= turn! 2)) (and (= turn 2) (= x! (- x 1)) (= y! (- y 1)) (= z! z) (= c! c) (= k! k) (= turn! 2)) (and (= turn 2) (= x! (- x 1)) (= y! (- y 1)) (= z! z) (= c! c) (= k! k) (= turn! 3)) (and (or (> turn 2) (< turn 0)) (= x! x) (= y! y) (= z! (+ x y)) (= c! c) (= k! k) (= turn! 0))))
(define-fun post_fun ((x Int) (y Int) (z Int) (c Int) (k Int) (turn Int)) Bool
    (= x y))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

