(set-logic LIA)

(synth-inv inv-f ((x Int) (y Int) (n Int)))

(declare-primed-var x Int)
(declare-primed-var y Int)
(declare-primed-var n Int)

(define-fun pre-f ((x Int) (y Int) (n Int)) Bool
  (and (>= n 0) (and (= x n) (= y 0))))

(define-fun trans-f ((x Int) (y Int) (n Int) (x! Int) (y! Int) (n! Int)) Bool
  (and (> x 0) (and (= n! n) (and (= y! (+ y 1)) (= x! (- x 1))))))

(define-fun post-f ((x Int) (y Int) (n Int)) Bool
  (or (> x 0) (= y n)))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)