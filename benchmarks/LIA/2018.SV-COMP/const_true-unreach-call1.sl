; From: https://github.com/sosy-lab/sv-benchmarks/blob/master/c/loop-acceleration/const_true-unreach-call1.c

(set-logic LIA)

(synth-inv inv-f ((x Int) (y Int)))

(declare-primed-var x Int)
(declare-primed-var y Int)

(define-fun pre-f ((x Int) (y Int)) Bool
  (and (= x 1) (= y 0)))

(define-fun trans-f ((x Int) (y Int) (x! Int) (y! Int)) Bool
  (and (< y 1024) (and (= x! 0) (= y! (+ y 1)))))

(define-fun post-f ((x Int) (y Int)) Bool
  (or (< y 1024) (= x 0)))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)
