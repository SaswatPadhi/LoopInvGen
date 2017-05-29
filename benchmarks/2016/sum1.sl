(set-logic LIA)

(synth-inv inv-f ((i Int) (n Int) (sn Int)))

(declare-primed-var i Int)
(declare-primed-var n Int)
(declare-primed-var sn Int)

(define-fun pre-f ((i Int) (n Int) (sn Int)) Bool
(and (= sn 0) (= i 1)))


(define-fun trans-f ((i Int) (n Int) (sn Int) (i! Int) (n! Int) (sn! Int) ) Bool
(and (= n! n) (and (= i! (+ i 1)) (and (<= i n) (= sn! (+ sn 1))))))

(define-fun post-f ((i Int) (n Int) (sn Int)) Bool
(or (<= i n) (or (= sn n) (= sn 0))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)