; benchmark adapted from page 26 of https://www.yumpu.com/de/document/read/43705376/berechnung-von-polynomiellen-invarianten

(set-logic NIA)

(synth-inv inv-f ((z Int) (k Int) (x Int) (y Int)))

(declare-primed-var z Int)
(declare-primed-var k Int)
(declare-primed-var x Int)
(declare-primed-var y Int)

(define-fun pre-f ((z Int) (k Int) (x Int) (y Int)) Bool
  (and (>= z 1) (= k 0) (= x 1) (= y 1)))

(define-fun trans-f ((z Int) (k Int) (x Int) (y Int)
                     (z! Int) (k! Int) (x! Int) (y! Int)) Bool
  (and (= x! (+ (* x z) 1))
       (= y! (* y z))
       (= k! (+ k 1))))
 
(define-fun post-f ((z Int) (k Int) (x Int) (y Int)) Bool
  (and (= y (pow z (- k 1)))
       (= x (div (- (pow z (+ k 1)) 1) (- z 1)))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)