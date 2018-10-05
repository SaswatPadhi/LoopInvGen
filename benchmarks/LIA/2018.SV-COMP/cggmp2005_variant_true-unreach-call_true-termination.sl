; From: https://github.com/sosy-lab/sv-benchmarks/blob/master/c/loop-lit/cggmp2005_variant_true-unreach-call_true-termination.c

(set-logic LIA)

(synth-inv inv_fun ((lo Int) (mid Int) (hi Int)))

(declare-primed-var lo Int)
(declare-primed-var mid Int)
(declare-primed-var hi Int)

(define-fun pre_fun ((lo Int) (mid Int) (hi Int)) Bool
  (and (= lo 0) (and (> mid 0) (= hi (* 2 mid)))))

(define-fun trans_fun ((lo Int) (mid Int) (hi Int)
                     (lo! Int) (mid! Int) (hi! Int)) Bool
  (and (> mid 0)
       (= lo! (+ lo 1))
       (= hi! (- hi 1))
       (= mid! (- mid 1))))

(define-fun post_fun ((lo Int) (mid Int) (hi Int)) Bool
  (or (> mid 0) (= lo hi)))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)
