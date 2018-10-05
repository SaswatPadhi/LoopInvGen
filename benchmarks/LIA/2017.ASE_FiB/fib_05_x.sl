(set-logic LIA)

(synth-inv inv_fun ((x Int) (y Int) (i Int) (j Int)))

(declare-primed-var x Int)
(declare-primed-var y Int)
(declare-primed-var i Int)
(declare-primed-var j Int)

(define-fun pre_fun ((x Int) (y Int) (i Int) (j Int)) Bool
(and (= x 0) (= y 0) (= j 0) (= i 0) ))

(define-fun trans_fun ((x Int) (y Int) (i Int) (j Int) (x! Int) (y! Int) (i! Int) (j! Int)) Bool
(and (= x! (+ x 1)) (= y! (+ y 1)) (= i! (+ x! i)) 
(or (= j! (+ y! j)) (= j! (+ (+ y! j) 1)) ))
)

(define-fun post_fun ((x Int) (y Int) (i Int) (j Int)) Bool
(>= j i))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)
