; From: https://github.com/sosy-lab/sv-benchmarks/blob/master/c/loop-lit/jm2006_variant_true-unreach-call_true-termination.c

(set-logic LIA)

(synth-inv inv_fun ((i Int) (j Int) (x Int) (y Int) (z Int)))

(declare-primed-var i Int)
(declare-primed-var j Int)
(declare-primed-var x Int)
(declare-primed-var y Int)
(declare-primed-var z Int)

(define-fun pre_fun ((i Int) (j Int) (x Int) (y Int) (z Int)) Bool
  (and (>= i 0) (>= j 0)
       (= z 0) (= x i) (= y j)))

(define-fun trans_fun ((i Int) (j Int) (x Int) (y Int) (z Int)
                     (i! Int) (j! Int) (x! Int) (y! Int) (z! Int)) Bool
  (and (not (= x 0))
       (= i! i) (= j! j)
       (= x! (- x 1))
       (= y! (- y 2))
       (= z! (+ z 1))))

(define-fun post_fun ((i Int) (j Int) (x Int) (y Int) (z Int)) Bool
  (or (not (= x 0)) (=> (= i j) (= y (- 0 z)))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)
