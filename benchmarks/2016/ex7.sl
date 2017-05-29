(set-logic LIA)

(synth-inv inv-f ((x Int) (y Int) (i Int)))

(declare-primed-var x Int)
(declare-primed-var y Int)
(declare-primed-var i Int)

(define-fun pre-f ((x Int) (y Int) (i Int)) Bool
(and (and (and (= i 0) (>= x 0)) (>= y 0)) (>= x y)))


(define-fun trans-f ((x Int) (y Int) (i Int) (x! Int) (y! Int) (i! Int)) Bool
(and (and (< i y) (= i! (+ i 1))) (and (= y! y) (= x! x))))

(define-fun post-f ((x Int) (y Int) (i Int)) Bool
(not (and (< i y) (or (>= i x) (> 0 i)))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)