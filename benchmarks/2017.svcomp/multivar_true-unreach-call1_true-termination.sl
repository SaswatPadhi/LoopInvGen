; From: https://github.com/sosy-lab/sv-benchmarks/blob/master/c/loop-acceleration/multivar_true-unreach-call1_true-termination.c

(set-logic LIA)

(synth-inv inv-f ((x Int) (y Int)))

(declare-primed-var x Int)
(declare-primed-var y Int)

(define-fun pre-f ((x Int) (y Int)) Bool
  (= y x))

(define-fun trans-f ((x Int) (y Int) (x! Int) (y! Int)) Bool
  (and (< x 1024) (and (= x! (+ x 1)) (= y! (+ y 1)))))

(define-fun post-f ((x Int) (y Int)) Bool
  (or (< x 1024) (= x y)))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)
