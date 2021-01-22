(set-logic LRA)

(synth-inv inv_fun ((x Real) (y Real) (xa Real) (ya Real)))

(define-fun pre_fun ((x Real) (y Real) (xa Real) (ya Real)) Bool
    (and (= xa 0.) (= ya 0.)))
(define-fun trans_fun ((x Real) (y Real) (xa Real) (ya Real) (x! Real) (y! Real) (xa! Real) (ya! Real)) Bool
    (and (= x! (+ 1. (+ xa (* 2. ya)))) (or (= y! (+ (- ya (* 2. xa)) x!)) (= y! (- (- ya (* 2. xa)) x!))) (= xa! (- x! (* 2. y!))) (= ya! (+ (* 2. x!) y!))))
(define-fun post_fun ((x Real) (y Real) (xa Real) (ya Real)) Bool
    (>= (+ xa (* 2. ya)) 0.))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)