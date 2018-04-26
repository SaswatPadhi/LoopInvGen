; From: http://www.cmi.ac.in/~madhukar/fmcad15/benchmarks/dagger/ex1.c

(set-logic LIA)

(synth-inv inv-f ((x Int) (y Int) (xa Int) (ya Int)))

(declare-primed-var x Int)
(declare-primed-var y Int)
(declare-primed-var xa Int)
(declare-primed-var ya Int)

(define-fun pre-f ((x Int) (y Int) (xa Int) (ya Int)) Bool
  (and (= xa 0) (= ya 0)))

(define-fun trans-f ((x Int) (y Int) (xa Int) (ya Int)
                     (x! Int) (y! Int) (xa! Int) (ya! Int)) Bool
  (and (= x! (+ 1 (+ xa (* 2 ya))))
       (or (= y! (+ (- ya (* 2 xa)) x!))
           (= y! (- (- ya (* 2 xa)) x!)))
       (= xa! (- x! (* 2 y!)))
       (= ya! (+ (* 2 x!) y!))))

(define-fun post-f ((x Int) (y Int) (xa Int) (ya Int)) Bool
  (>= (+ xa (* 2 ya)) 0))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)
