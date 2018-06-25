(set-logic LIA)

(synth-inv inv-f ((x Int) (y Int) (i Int) (n Int)))

(declare-primed-var x Int)
(declare-primed-var y Int)
(declare-primed-var i Int)
(declare-primed-var n Int)

(define-fun pre-f ((x Int) (y Int) (i Int) (n Int)) Bool
  (and (= x 0) (= y 0) (= i 0)))

(define-fun trans-f ((x Int) (y Int) (i Int) (n Int)
                     (x! Int) (y! Int) (i! Int) (n! Int)) Bool
  (and (< i n)
       (= i! (+ i 1)) (= x! (+ x 1)) (= n! n)
       (or (and (exists ((k Int)) (= i (* 2 k))) (= y! (+ y 1)))
           (and (exists ((k Int)) (= i (+ 1 (* 2 k)))) (= y! y)))))

(define-fun post-f ((x Int) (y Int) (i Int) (n Int)) Bool
  (or (< i n)
      (or (exists ((k Int)) (= i (+ 1 (* 2 k))))
          (= x (* 2 y)))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)