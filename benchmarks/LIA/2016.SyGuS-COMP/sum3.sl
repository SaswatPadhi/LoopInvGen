(set-logic LIA)

(synth-inv inv-f ((x Int) (sn Int)))

(declare-primed-var x Int)
(declare-primed-var sn Int)

(define-fun pre-f ((x Int) (sn Int)) Bool
(and (= sn 0) (= x 0)))


(define-fun trans-f ((x Int) (sn Int) (x! Int) (sn! Int) ) Bool
(and (= x! (+ x 1)) (= sn! (+ sn 1))))

(define-fun post-f ((x Int) (sn Int)) Bool
(or (= sn x) (= sn -1)))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)