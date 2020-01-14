(set-logic NIA)

(synth-inv InvF ((x1 Int) (x2 Int) (y1 Int) (y2 Int) (y3 Int)))

(define-fun PreF ((x1 Int) (x2 Int) (y1 Int) (y2 Int) (y3 Int)) Bool
    (and (>= x1 0) (> x2 0) (= y1 0) (= y2 0) (= y3 x1)))
(define-fun TransF ((x1 Int) (x2 Int) (y1 Int) (y2 Int) (y3 Int) (x1! Int) (x2! Int) (y1! Int) (y2! Int) (y3! Int)) Bool
    (and (not (= y3 0)) (= x1! x1) (= x2! x2) (or (and (= x2 (+ y2 1)) (= y1! (+ y1 1)) (= y2! 0) (= y3! (- y3 1))) (and (not (= x2 (+ y2 1))) (= y1! y1) (= y2! (+ y2 1)) (= y3! (- y3 1))))))
(define-fun PostF ((x1 Int) (x2 Int) (y1 Int) (y2 Int) (y3 Int)) Bool
    (=> (= y3 0) (and (= y2 (mod x1 x2)) (= y1 (div x1 x2)))))

(inv-constraint InvF PreF TransF PostF)

(check-synth)

