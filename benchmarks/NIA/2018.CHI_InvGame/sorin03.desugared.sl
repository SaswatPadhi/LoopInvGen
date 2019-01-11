; Benchmark adapted from "sorin03.desugared.bpl"

(set-logic NIA)

(synth-inv inv-f ((n Int) (s Int) (i Int) (j Int)))

(declare-primed-var n Int)
(declare-primed-var s Int)
(declare-primed-var i Int)
(declare-primed-var j Int)

(define-fun pre-f ((n Int) (s Int) (i Int) (j Int)) Bool
  (and (<= 1 n) (<= n 1000) (= s 0) (= j 0) (= i 1)))

(define-fun trans-f ((n Int) (s Int) (i Int) (j Int)
                     (n! Int) (s! Int) (i! Int) (j! Int)) Bool
  (and (<= i n) (= s! (+ s i)) (= j! i) (= i! (+ i 1)) (= n! n)))

(define-fun post-f ((n Int) (s Int) (i Int) (j Int)) Bool
  (or (<= i n) (= (* 2 s) (* n (+ n 1)))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)