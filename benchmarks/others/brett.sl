(set-logic LIA)

(synth-inv inv-f ((p Int) (c Int) (cl Int)))

(declare-primed-var p Int)
(declare-primed-var c Int)
(declare-primed-var cl Int)

(define-fun pre-f ((p Int) (c Int) (cl Int)) Bool
  (and (= p 0) (= c cl)))

(define-fun trans-f ((p Int) (c Int) (cl Int)
                     (p! Int) (c! Int) (cl! Int)) Bool
  (and (and (< p 4) (> cl 0))
       (and (= cl! (- cl 1))
            (= p! (+ p 1))
            (= c! c))))

(define-fun post-f ((p Int) (c Int) (cl Int)) Bool
  (or (and (< p 4) (> cl 0))
      (or (< c 4) (= p 4))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)
