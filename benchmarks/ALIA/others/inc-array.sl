(set-logic ALIA)

(synth-inv inv_fun ((x (Array Int Int))))

(define-fun pre_fun ((x (Array Int Int))) Bool
    (= 1 (select x 0)))
(define-fun trans_fun ((x (Array Int Int)) (x! (Array Int Int))) Bool
    (and (< (select x 0) 100) (= x! (store x 0 (+ (select x 0) 2)))))
(define-fun post_fun ((x (Array Int Int))) Bool
    (or (not (>= (select x 0) 100)) (= (select x 0) 101)))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

