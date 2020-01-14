(set-logic LIA)

(synth-inv inv_fun ((x1 Int) (x2 Int) (x3 Int) (d1 Int) (d2 Int) (d3 Int) (v1 Int) (v2 Int) (v3 Int)))

(define-fun pre_fun ((x1 Int) (x2 Int) (x3 Int) (d1 Int) (d2 Int) (d3 Int) (v1 Int) (v2 Int) (v3 Int)) Bool
    (and (= d1 1) (and (= d2 1) (= d3 1))))
(define-fun trans_fun ((x1 Int) (x2 Int) (x3 Int) (d1 Int) (d2 Int) (d3 Int) (v1 Int) (v2 Int) (v3 Int) (x1! Int) (x2! Int) (x3! Int) (d1! Int) (d2! Int) (d3! Int) (v1! Int) (v2! Int) (v3! Int)) Bool
    (or (and (and (= x2! x2) (and (= x3! x3) (and (= d1! d1) (and (= d2! d2) (= d3! d3))))) (and (> x1 0) (and (> x2 0) (and (> x3 0) (= x1! (+ x1 (- 0 d1))))))) (or (and (and (= x1! x1) (and (= x3! x3) (and (= d1! d1) (and (= d2! d2) (= d3! d3))))) (and (> x1 0) (and (> x2 0) (and (> x3 0) (= x2! (+ x2 (- 0 d2))))))) (and (and (= x1! x1) (and (= x2! x2) (and (= d1! d1) (and (= d2! d2) (= d3! d3))))) (and (> x1 0) (and (> x2 0) (and (> x3 0) (= x3! (+ x3 (- 0 d3))))))))))
(define-fun post_fun ((x1 Int) (x2 Int) (x3 Int) (d1 Int) (d2 Int) (d3 Int) (v1 Int) (v2 Int) (v3 Int)) Bool
    (or (< x1 0) (or (< x2 0) (or (< x3 0) (or (= x1 0) (or (= x2 0) (= x3 0)))))))

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)

