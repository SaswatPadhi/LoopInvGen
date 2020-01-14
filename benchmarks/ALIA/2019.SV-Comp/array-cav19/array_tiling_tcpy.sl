(set-logic ALIA)

(synth-inv inv_fun ((a (Array Int Int)) (acopy (Array Int Int)) (s Int) (i Int)))

(define-fun pre_fun ((a (Array Int Int)) (acopy (Array Int Int)) (s Int) (i Int)) Bool
    (and (> s 1) (= i 0)))
(define-fun trans_fun ((a (Array Int Int)) (acopy (Array Int Int)) (s Int) (i Int) (a! (Array Int Int)) (acopy! (Array Int Int)) (s! Int) (i! Int)) Bool
    (and (< i s) (= i! (+ i 1)) (= s! s) (= acopy! (store (store acopy i (select a i)) (- (* 2 s) (+ i 1)) (select a (- (* 2 s) (+ i 1)))))))
(define-fun post_fun ((a (Array Int Int)) (acopy (Array Int Int)) (s Int) (i Int)) Bool
    (or (< i s) (forall ((j Int)) (=> (and (>= j 0) (< j (* 2 s))) (= (select acopy j) (select a j))))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

