(set-logic LIA)

(synth-inv inv-f ((i Int) (j Int) (k Int) (m Int) (n Int) (x Int) (y Int)))

(declare-primed-var i Int)
(declare-primed-var j Int)
(declare-primed-var k Int)
(declare-primed-var m Int)
(declare-primed-var n Int)
(declare-primed-var x Int)
(declare-primed-var y Int)

(define-fun pre-f ((i Int) (j Int) (k Int) (m Int) (n Int) (x Int) (y Int)) Bool
  (and (= k (+ x y)) (and (= m 0) (= j 0))))

(define-fun trans-f ((i Int) (j Int) (k Int) (m Int) (n Int) (x Int) (y Int)
                     (i! Int) (j! Int) (k! Int) (m! Int) (n! Int) (x! Int) (y! Int)) Bool
  (and (< j n) (and (= i! i) (and (= k! k) (and (= n! n) 
               (and (= j! (+ j 1))
                    (and (or (= m! m) (= m! j))
                         (or (and (= j i) (and (= x! (+ x 1)) (= y! (- y 1))))
                             (and (not (= j i)) (and (= x! (- x 1)) (= y! (+ y 1))))))))))))

(define-fun post-f ((i Int) (j Int) (k Int) (m Int) (n Int) (x Int) (y Int)) Bool
  (and (= k (+ x y))
       (or (not (> n 0)) (and (<= 0 m) (< m n)))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)