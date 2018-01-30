; Benchmark adapted from "gauss_sum_true-unreach-call.c"

(set-logic NIA)

(synth-inv inv-f ((n Int) (s Int) (i Int)))

(declare-primed-var n Int)
(declare-primed-var s Int)
(declare-primed-var i Int)

(define-fun pre-f ((n Int) (s Int) (i Int)) Bool
  (and (>= n 1) (<= n 1000) (= s 0) (= i 1)))

(define-fun trans-f ((n Int) (s Int) (i Int)
                     (n! Int) (s! Int) (i! Int)) Bool
  (and (<= i n) (= i! (+ i 1)) (= s! (+ s i)) (= n! n)))

(define-fun post-f ((n Int) (s Int) (i Int)) Bool
  (or (<= i n) (= (* s 2) (* n (+ n 1)))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)
