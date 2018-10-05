; From: Evaluation Example 4 of https://hal.inria.fr/inria-00615623/document

(set-logic LIA)

(synth-inv inv_fun ((i Int) (b Int) (n Int)))

(declare-primed-var i Int)
(declare-primed-var b Int)
(declare-primed-var n Int)

(define-fun pre_fun ((i Int) (b Int) (n Int)) Bool
  (and (= i 0) (< i n)))

(define-fun trans_fun ((i Int) (b Int) (n Int)
                     (i! Int) (b! Int) (n! Int)) Bool
  (and (< i n)
       (= n! n)
       (or (and (= b! 0) (= i! i))
           (and (not (= b! 0)) (= i! (+ i 1))))))

(define-fun post_fun ((i Int) (b Int) (n Int)) Bool
  (or (< i n)
      (and (= i n) (not (= b 0)))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)
