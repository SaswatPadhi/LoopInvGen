; Benchmark adapted from "prod-bin.desugared.bpl"

(set-logic NIA)

(synth-inv inv-f ((a Int) (b Int) (x Int) (y Int) (z Int)))

(declare-primed-var a Int)
(declare-primed-var b Int)
(declare-primed-var x Int)
(declare-primed-var y Int)
(declare-primed-var z Int)

(define-fun pre-f ((a Int) (b Int) (x Int) (y Int) (z Int)) Bool
  (and (>= a 0) (>= b 0) (= x a) (= y b) (= z 0)))

(define-fun trans-f ((a Int) (b Int) (x Int) (y Int) (z Int)
                     (a! Int) (b! Int) (x! Int) (y! Int) (z! Int)) Bool
  (and (not (= 0 y)) (= a! a) (= b! b)
    (or (and (not (= 1 (mod y 2))) (= x! (* 2 x)) (= y! (div y 2)))
        (and (= 1 (mod y 2)) (= x! x) (= z! (+ z x)) (= y! (- y 1))))))

(define-fun post-f ((a Int) (b Int) (x Int) (y Int) (z Int)) Bool
  (or (not (= y 0)) (= z (* a b))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)
