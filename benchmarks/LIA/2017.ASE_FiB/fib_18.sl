(set-logic LIA)

(synth-inv inv_fun ((b Int) (j Int) (n Int) (flag Int)))

(declare-primed-var b Int)
(declare-primed-var j Int)
(declare-primed-var n Int)
(declare-primed-var flag Int)

(define-fun pre_fun ((b Int) (j Int) (n Int) (flag Int)) Bool
(and (= j 0) (> n 0) (= b 0) ))

(define-fun trans_fun ((b Int) (j Int) (n Int) (flag Int) (b! Int) (j! Int) (n! Int) (flag! Int)) Bool
(or (and (< b n) (= flag 1) (= j! (+ j 1)) (= b! (+ b 1)) (= n! n) (= flag! flag))
(and (< b n) (not (= flag 1)) (= j! j) (= b! (+ b 1)) (= n! n) (= flag! flag))
(and (>= b n) (= j! j) (= b! b) (= n! n) (= flag! flag))
))

(define-fun post_fun ((b Int) (j Int) (n Int) (flag Int)) Bool
(=> (not (< b n)) (or (not (= flag 1)) (= j n)))
)

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)
