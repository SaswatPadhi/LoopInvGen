(set-logic LIA)

(synth-inv inv-f ((x Int) (y Int) (i Int) (j Int)))

(declare-primed-var x Int)
(declare-primed-var y Int)
(declare-primed-var i Int)
(declare-primed-var j Int)

(define-fun pre-f ((x Int) (y Int) (i Int) (j Int)) Bool
  (and (= j 0) (and (= i 0) (and (= x 0) (= y 0)))))

(define-fun trans-f ((x Int) (y Int) (i Int) (j Int)
                     (x! Int) (y! Int) (i! Int) (j! Int)) Bool
  (and (= x! (+ x 1)) (and (= y! (+ y 1)) (and (= i! (+ i (+ x 1)))
                                               (or (= j! (+ j (+ y 1)))
                                                   (= j! (+ j (+ y 2))))))))

(define-fun post-f ((x Int) (y Int) (i Int) (j Int)) Bool
  (>= j i))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)