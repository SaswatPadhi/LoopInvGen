(set-logic LIA)

(synth-inv inv-f ((conf_0 Int) (m Int) (n Int) (x Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (m_0 Int) (m_1 Int) (m_2 Int) (m_3 Int) (m_4 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)))

(define-fun pre-f ((conf_0 Int) (m Int) (n Int) (x Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (m_0 Int) (m_1 Int) (m_2 Int) (m_3 Int) (m_4 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)) Bool
    (and (= conf_0 conf_0_0) (= m m_1) (= x x_1) (= conf_0_0 2) (= x_1 0) (= m_1 0)))
(define-fun trans-f ((conf_0 Int) (m Int) (n Int) (x Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (m_0 Int) (m_1 Int) (m_2 Int) (m_3 Int) (m_4 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (conf_0! Int) (m! Int) (n! Int) (x! Int) (tmp! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (conf_0_3! Int) (conf_0_4! Int) (m_0! Int) (m_1! Int) (m_2! Int) (m_3! Int) (m_4! Int) (n_0! Int) (x_0! Int) (x_1! Int) (x_2! Int) (x_3! Int)) Bool
    (or (and (= conf_0_1 conf_0) (= m_2 m) (= x_2 x) (= conf_0_1 conf_0!) (= m_2 m!) (= x_2 x!) (= n n_0) (= n! n_0) (= conf_0 conf_0!) (= m m!) (= tmp tmp!)) (and (= conf_0_1 conf_0) (= m_2 m) (= x_2 x) (< x_2 n_0) (= m_3 x_2) (= conf_0_2 (- 161 conf_0_1)) (= conf_0_3 conf_0_2) (= m_4 m_3) (= x_3 (+ x_2 1)) (= conf_0_4 (+ conf_0_3 483)) (= conf_0_4 conf_0!) (= m_4 m!) (= x_3 x!) (= n n_0) (= n! n_0) (= tmp tmp!)) (and (= conf_0_1 conf_0) (= m_2 m) (= x_2 x) (< x_2 n_0) (= conf_0_3 conf_0_1) (= m_4 m_2) (= x_3 (+ x_2 1)) (= conf_0_4 (+ conf_0_3 483)) (= conf_0_4 conf_0!) (= m_4 m!) (= x_3 x!) (= n n_0) (= n! n_0) (= tmp tmp!))))
(define-fun post-f ((conf_0 Int) (m Int) (n Int) (x Int) (tmp Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (conf_0_3 Int) (conf_0_4 Int) (m_0 Int) (m_1 Int) (m_2 Int) (m_3 Int) (m_4 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)) Bool
    (or (not (and (= conf_0 conf_0_1) (= m m_2) (= n n_0) (= x x_2))) (not (and (not (< x_2 n_0)) (> n_0 0) (not (>= m_2 0))))))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

