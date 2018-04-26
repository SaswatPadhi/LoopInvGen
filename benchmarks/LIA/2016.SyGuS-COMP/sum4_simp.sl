(set-logic LIA)

(synth-inv inv-f ((i Int) (sn Int) (size Int)))

(declare-primed-var i Int)
(declare-primed-var sn Int)
(declare-primed-var size Int)

(define-fun pre-f ((i Int) (sn Int) (size Int)) Bool
(and (= sn 0) (= i 1)))


(define-fun trans-f ((i Int) (sn Int) (size Int) (i! Int) (sn! Int) (size! Int)) Bool
(and (= size! size) (and (= i! (+ i 1)) (and (<= i size) (= sn! (+ sn 1))))))

(define-fun post-f ((i Int) (sn Int) (size Int)) Bool
(or (<= i size) (or (= sn size) (= sn 0))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)