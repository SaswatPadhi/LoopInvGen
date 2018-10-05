; From: https://github.com/sosy-lab/sv-benchmarks/blob/master/c/loop-acceleration/underapprox_true-unreach-call2_true-termination.c

(set-logic LIA)

(synth-inv inv_fun ((x Int) (y Int)))

(declare-primed-var x Int)
(declare-primed-var y Int)

(define-fun pre_fun ((x Int) (y Int)) Bool
  (and (= x 0) (= y 1)))

(define-fun trans_fun ((x Int) (y Int) (x! Int) (y! Int)) Bool
  (and (< x 6) (and (= x! (+ x 1)) (= y! (* y 2)))))

(define-fun post_fun ((x Int) (y Int)) Bool
  (or (< x 6) (= x 6)))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)
