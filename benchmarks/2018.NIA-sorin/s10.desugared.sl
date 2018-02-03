; Benchmark adapted from "s10.desugared.bpl"

(set-logic NIA)

(synth-inv inv-f ((i Int) (j Int) (k Int)))

(declare-primed-var i Int)
(declare-primed-var j Int)
(declare-primed-var k Int)

(define-fun pre-f ((i Int) (j Int) (k Int)) Bool
  (and (= j 0) (= i 10)))

(define-fun trans-f ((i Int) (j Int) (k Int)
                     (i! Int) (j! Int) (k! Int)) Bool
  (and (< j 1000) (= i! (+ i k)) (= j! (+ j 1)) (= k! k)))

(define-fun post-f ((i Int) (j Int) (k Int)) Bool
  (or (< j 1000) (= i (+ 10 (* k j)))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)