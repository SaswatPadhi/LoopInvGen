(set-logic LIA)

(synth-inv inv_fun ((a Int) (b Int) (res Int) (cnt Int)))

(define-fun pre_fun ((a Int) (b Int) (res Int) (cnt Int)) Bool
    (and (<= a 1000000) (<= 0 b) (<= b 1000000) (= res a) (= cnt b)))
(define-fun trans_fun ((a Int) (b Int) (res Int) (cnt Int) (a! Int) (b! Int) (res! Int) (cnt! Int)) Bool
    (and (> cnt 0) (= cnt! (- cnt 1)) (= res! (+ res 1)) (= a! a) (= b! b)))
(define-fun post_fun ((a Int) (b Int) (res Int) (cnt Int)) Bool
    (or (> cnt 0) (= res (+ a b))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

