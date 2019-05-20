; benchmark adapted from page 28 https://www.yumpu.com/de/document/read/43705376/berechnung-von-polynomiellen-invarianten

(set-logic NIA)

(synth-inv inv-f ((x Int) (y Int) (i Int) (k Int)))

(declare-primed-var x Int)
(declare-primed-var y Int)
(declare-primed-var i Int)
(declare-primed-var k Int)

(define-fun pre-f ((x Int) (y Int) (i Int) (k Int)) Bool
    (and (= x 0) (= y 0) (= i 0) (>= k 0)))

(define-fun trans-f ((x Int) (y Int) (i Int) (k Int)
                     (x! Int) (y! Int) (i! Int) (k! Int)) Bool
  (and (< i k) (= k! k)
       (= i! (+ i 1))
       (= y! (+ y 1))
       (= x! (+ x y!))))

(define-fun post-f ((x Int) (y Int) (i Int) (k Int)) Bool
  (or (< i k)
      (and (= y k)
           (= (* 2 x) (+ (* y y) y)))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)