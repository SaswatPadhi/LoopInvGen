(set-logic LIA)

(synth-inv inv-f ((x Int) (y Int) (failed Bool)))

(declare-primed-var x Int)
(declare-primed-var y Int)
(declare-primed-var failed Bool)

(define-fun pre-f ((x Int) (y Int) (failed Bool)) Bool
  (and (= x 0) (= failed false)))

(define-fun trans-f ((x Int) (y Int) (failed Bool)
                     (x! Int) (y! Int) (failed! Bool)) Bool
  (and (not (= y 0))
       (or (and (< y 0) (= x! (- x 1)) (= y! (+ y 1)))
           (and (>= y 0) (= x! (+ x 1)) (= y! (- y 1))))
       (or (and (= x! 0) (= failed! true))
           (and (not (= x! 0)) (= failed! failed)))))

(define-fun post-f ((x Int) (y Int) (failed Bool)) Bool
  (or (not (= y 0))
      (= failed false)))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)
