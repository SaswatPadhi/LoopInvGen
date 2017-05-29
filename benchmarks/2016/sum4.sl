(set-logic LIA)

(synth-inv inv-f ((i Int) (sn Int)))

(declare-primed-var i Int)
(declare-primed-var sn Int)

(define-fun pre-f ((i Int) (sn Int)) Bool
(and (= sn 0) (= i 1)))


(define-fun trans-f ((i Int) (sn Int) (i! Int) (sn! Int) ) Bool
(and (= i! (+ i 1)) (and (<= i 8) (= sn! (+ sn 1)))))

(define-fun post-f ((i Int) (sn Int)) Bool
(or (<= i 8) (or (= sn 8) (= sn 0))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)