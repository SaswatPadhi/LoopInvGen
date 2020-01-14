(set-logic LIA)

(synth-inv inv_fun ((x1 Int) (x2 Int) (x3 Int) (v1 Int) (v2 Int) (v3 Int) (t Int) (RETURN Int)))

(define-fun pre_fun ((x1 Int) (x2 Int) (x3 Int) (v1 Int) (v2 Int) (v3 Int) (t Int) (RETURN Int)) Bool
    (and (= RETURN 0) (= x1 100) (= x2 75) (= x3 (- 0 50)) (>= v3 0) (<= v1 5) (>= (- v1 v3) 0) (= (- (- (* 2 v2) v1) v3) 0) (= t 0) (>= (+ v2 5) 0) (<= v2 5)))
(define-fun trans_fun ((x1 Int) (x2 Int) (x3 Int) (v1 Int) (v2 Int) (v3 Int) (t Int) (RETURN Int) (x1! Int) (x2! Int) (x3! Int) (v1! Int) (v2! Int) (v3! Int) (t! Int) (RETURN! Int)) Bool
    (and (= RETURN 0) (or (and (not (>= (+ v2 5) 0)) (= RETURN! 1)) (and (>= (+ v2 5) 0) (= RETURN! RETURN))) (or (and (not (<= v2 5)) (= RETURN! 1)) (and (<= v2 5) (= RETURN! RETURN))) (or (and (or (and (not (>= (- (- (* 2 x2) x1) x3) 0)) (= RETURN! 1)) (and (>= (- (- (* 2 x2) x1) x3) 0) (= RETURN! RETURN))) (= x1! (+ x1 v1)) (= x3! (+ x3 v3)) (= x2! (+ x2 v2)) (= v2! (- v2 1)) (= v1! v1) (= v3! v3) (= t! (+ t 1))) (and (or (and (not (<= (- (- (* 2 x2) x1) x3) 0)) (= RETURN! 1)) (and (<= (- (- (* 2 x2) x1) x3) 0) (= RETURN! RETURN))) (= x1! (+ x1 v1)) (= x3! (+ x3 v3)) (= x2! (+ x2 v2)) (= v2! (+ v2 1)) (= v1! v1) (= v3! v3) (= t! (+ t 1))))))
(define-fun post_fun ((x1 Int) (x2 Int) (x3 Int) (v1 Int) (v2 Int) (v3 Int) (t Int) (RETURN Int)) Bool
    (=> (= RETURN 0) (and (<= v1 5) (>= (+ (* 2 v2) (* 2 t)) (+ v1 v3)) (>= (+ (* 5 t) 75) x2) (<= v2 6) (>= v3 0) (>= (+ v2 6) 0) (>= (+ x2 (* 5 t)) 75) (>= (- (+ v1 v3 (* 2 t)) (* 2 v2)) 0) (>= (- v1 v3) 0))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

