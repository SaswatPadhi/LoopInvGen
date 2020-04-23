(set-logic LIA)

(synth-inv inv_fun ((c Int) (i Int)))

(define-fun pre_fun ((c Int) (i Int)) Bool
    (= i 0))
(define-fun trans_fun ((c Int) (i Int) (c! Int) (i! Int)) Bool
    (and (> c 48) (and (< c 57) (= i! (+ (+ i i) (- c 48))))))
(define-fun post_fun ((c Int) (i Int)) Bool
    (or (> c 57) (or (< c 48) (>= i 0))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

