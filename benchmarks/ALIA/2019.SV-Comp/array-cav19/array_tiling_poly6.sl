(set-logic ALIA)

(synth-inv inv_fun ((a (Array Int Int)) (i Int) (s Int)))

(define-fun pre_fun ((a (Array Int Int)) (i Int) (s Int)) Bool
    (and (= i 0) (> s 1)))
(define-fun trans_fun ((a (Array Int Int)) (i Int) (s Int) (a! (Array Int Int)) (i! Int) (s! Int)) Bool
    (and (< i (* 2 s)) (= i! (+ i! 1)) (= s! s) (ite (< i s) (= a! (store a i (* (- i 1) (+ i 1)))) (= a! (store a (- i s) (- (select a (- i s)) (* (- i s) (- i s))))))))
(define-fun post_fun ((a (Array Int Int)) (i Int) (s Int)) Bool
    (or (< i (* 2 s)) (forall ((j Int)) (=> (and (>= j 0) (< j s)) (= (- 1) (select a j))))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

