(set-logic SLIA)

(synth-inv inv-f ((i Int) (r String)))

(declare-primed-var i Int)
(declare-primed-var r String)

(define-fun pre-f ((i Int) (r String)) Bool
  (and (= i 0) (= r 'a')))

(define-fun trans-f ((i Int) (r String) (i! Int) (r! String)) Bool
  (or (and (= i! (+ i 1) (= r! (str.++ '<' r '>'))))
      (and (= i! i) (= r! r))))

(define-fun post-f ((i Int) (r String)) Bool
  (and (= (str.len r) (+ (* 2 i) 1))
       (=> (> i 0) (str.contains r '<a>'))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)