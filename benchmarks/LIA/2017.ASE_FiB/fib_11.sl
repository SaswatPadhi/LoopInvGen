(set-logic LIA)

(synth-inv inv_fun ((x Int) (i Int) (j Int)))

(declare-primed-var x Int)
(declare-primed-var i Int)
(declare-primed-var j Int)

(define-fun pre_fun ((x Int) (i Int) (j Int)) Bool
(and (= j 0) (> x 0) (= i 0) ))

(define-fun trans_fun ((x Int) (i Int) (j Int) (x! Int) (i! Int) (j! Int)) Bool
(or (and (< i x) (= j! (+ j 2)) (= i! (+ i 1)) (= x! x) )
(and (>= i x) (= j! j) (= i! i) (= x! x) )
))

(define-fun post_fun ((x Int) (i Int) (j Int)) Bool
(=> (not (< i x)) (= j (* 2 x))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)
