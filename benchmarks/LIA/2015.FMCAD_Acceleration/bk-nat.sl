(set-logic LIA)

(synth-inv inv_fun ((invalid Int) (unowned Int) (nonexclusive Int) (exclusive Int) (RETURN Int)))

(define-fun pre_fun ((invalid Int) (unowned Int) (nonexclusive Int) (exclusive Int) (RETURN Int)) Bool
    (and (ite (>= invalid 1) (= RETURN 0) (= RETURN 1)) (ite (= unowned 0) (= RETURN 0) (= RETURN 1)) (ite (= nonexclusive 0) (= RETURN 0) (= RETURN 1)) (ite (= exclusive 0) (= RETURN 0) (= RETURN 1))))
(define-fun trans_fun ((invalid Int) (unowned Int) (nonexclusive Int) (exclusive Int) (RETURN Int) (invalid! Int) (unowned! Int) (nonexclusive! Int) (exclusive! Int) (RETURN! Int)) Bool
    (or (and (ite (not (>= invalid 1)) (= RETURN! 1) (= RETURN! RETURN)) (= nonexclusive! (+ nonexclusive exclusive)) (= exclusive! 0) (= invalid! (- invalid 1)) (= unowned! (+ unowned 1))) (and (ite (not (>= (+ nonexclusive unowned) 1)) (= RETURN! 1) (= RETURN! RETURN)) (= nonexclusive! 0) (= exclusive! (+ exclusive 1)) (= invalid! (- (+ invalid unowned nonexclusive) 1)) (= unowned! 0)) (and (ite (not (>= invalid 1)) (= RETURN! 1) (= RETURN! RETURN)) (= nonexclusive! 0) (= exclusive! 1) (= invalid! (- (+ invalid unowned! exclusive! nonexclusive!) 1)) (= unowned! 0))))
(define-fun post_fun ((invalid Int) (unowned Int) (nonexclusive Int) (exclusive Int) (RETURN Int)) Bool
    (=> (= RETURN 0) (and (>= exclusive 0) (>= nonexclusive 0) (>= unowned 0) (>= invalid 0) (>= (+ invalid unowned exclusive) 1))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

