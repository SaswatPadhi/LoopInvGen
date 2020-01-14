(set-logic LIA)

(define-fun __node_init_Sofar_0 ((Sofar.usr.X_a_0 Bool) (Sofar.usr.Y_a_0 Bool) (Sofar.res.init_flag_a_0 Bool)) Bool
    (and (= Sofar.usr.Y_a_0 Sofar.usr.X_a_0) Sofar.res.init_flag_a_0))
(define-fun __node_trans_Sofar_0 ((Sofar.usr.X_a_1 Bool) (Sofar.usr.Y_a_1 Bool) (Sofar.res.init_flag_a_1 Bool) (Sofar.usr.X_a_0 Bool) (Sofar.usr.Y_a_0 Bool) (Sofar.res.init_flag_a_0 Bool)) Bool
    (and (= Sofar.usr.Y_a_1 (and Sofar.usr.Y_a_0 Sofar.usr.X_a_1)) (not Sofar.res.init_flag_a_1)))
(define-fun __node_init_Store_0 ((Store.usr.Delta_a_0 Int) (Store.usr.Total_a_0 Int) (Store.res.init_flag_a_0 Bool)) Bool
    (let ((X1 0)) (and (= Store.usr.Total_a_0 (ite (and (< Store.usr.Delta_a_0 0) (> X1 0)) (+ X1 Store.usr.Delta_a_0) (ite (and (> Store.usr.Delta_a_0 0) (< X1 10)) (+ X1 Store.usr.Delta_a_0) X1))) Store.res.init_flag_a_0)))
(define-fun __node_trans_Store_0 ((Store.usr.Delta_a_1 Int) (Store.usr.Total_a_1 Int) (Store.res.init_flag_a_1 Bool) (Store.usr.Delta_a_0 Int) (Store.usr.Total_a_0 Int) (Store.res.init_flag_a_0 Bool)) Bool
    (let ((X1 Store.usr.Total_a_0)) (and (= Store.usr.Total_a_1 (ite (and (< Store.usr.Delta_a_1 0) (> X1 0)) (+ X1 Store.usr.Delta_a_1) (ite (and (> Store.usr.Delta_a_1 0) (< X1 10)) (+ X1 Store.usr.Delta_a_1) X1))) (not Store.res.init_flag_a_1))))
(define-fun __node_init_top_0 ((top.usr.Delta_a_0 Int) (top.usr.OK_a_0 Bool) (top.res.init_flag_a_0 Bool) (top.res.abs_0_a_0 Int) (top.res.abs_1_a_0 Bool) (top.res.abs_2_a_0 Bool) (top.res.inst_1_a_0 Bool) (top.res.inst_0_a_0 Bool)) Bool
    (and (= top.res.abs_1_a_0 (and (<= (- 1) top.usr.Delta_a_0) (<= top.usr.Delta_a_0 1))) (let ((X1 top.res.abs_0_a_0)) (and (= top.usr.OK_a_0 (=> top.res.abs_2_a_0 (and (<= 0 X1) (<= X1 20)))) (__node_init_Store_0 top.usr.Delta_a_0 top.res.abs_0_a_0 top.res.inst_1_a_0) (__node_init_Sofar_0 top.res.abs_1_a_0 top.res.abs_2_a_0 top.res.inst_0_a_0) top.res.init_flag_a_0))))
(define-fun __node_trans_top_0 ((top.usr.Delta_a_1 Int) (top.usr.OK_a_1 Bool) (top.res.init_flag_a_1 Bool) (top.res.abs_0_a_1 Int) (top.res.abs_1_a_1 Bool) (top.res.abs_2_a_1 Bool) (top.res.inst_1_a_1 Bool) (top.res.inst_0_a_1 Bool) (top.usr.Delta_a_0 Int) (top.usr.OK_a_0 Bool) (top.res.init_flag_a_0 Bool) (top.res.abs_0_a_0 Int) (top.res.abs_1_a_0 Bool) (top.res.abs_2_a_0 Bool) (top.res.inst_1_a_0 Bool) (top.res.inst_0_a_0 Bool)) Bool
    (and (= top.res.abs_1_a_1 (and (<= (- 1) top.usr.Delta_a_1) (<= top.usr.Delta_a_1 1))) (let ((X1 top.res.abs_0_a_1)) (and (= top.usr.OK_a_1 (=> top.res.abs_2_a_1 (and (<= 0 X1) (<= X1 20)))) (__node_trans_Store_0 top.usr.Delta_a_1 top.res.abs_0_a_1 top.res.inst_1_a_1 top.usr.Delta_a_0 top.res.abs_0_a_0 top.res.inst_1_a_0) (__node_trans_Sofar_0 top.res.abs_1_a_1 top.res.abs_2_a_1 top.res.inst_0_a_1 top.res.abs_1_a_0 top.res.abs_2_a_0 top.res.inst_0_a_0) (not top.res.init_flag_a_1)))))
(synth-inv str_invariant ((top.usr.Delta Int) (top.usr.OK Bool) (top.res.init_flag Bool) (top.res.abs_0 Int) (top.res.abs_1 Bool) (top.res.abs_2 Bool) (top.res.inst_1 Bool) (top.res.inst_0 Bool)))

(define-fun init ((top.usr.Delta Int) (top.usr.OK Bool) (top.res.init_flag Bool) (top.res.abs_0 Int) (top.res.abs_1 Bool) (top.res.abs_2 Bool) (top.res.inst_1 Bool) (top.res.inst_0 Bool)) Bool
    (and (= top.res.abs_1 (and (<= (- 1) top.usr.Delta) (<= top.usr.Delta 1))) (let ((X1 top.res.abs_0)) (and (= top.usr.OK (=> top.res.abs_2 (and (<= 0 X1) (<= X1 20)))) (__node_init_Store_0 top.usr.Delta top.res.abs_0 top.res.inst_1) (__node_init_Sofar_0 top.res.abs_1 top.res.abs_2 top.res.inst_0) top.res.init_flag))))
(define-fun trans ((top.usr.Delta Int) (top.usr.OK Bool) (top.res.init_flag Bool) (top.res.abs_0 Int) (top.res.abs_1 Bool) (top.res.abs_2 Bool) (top.res.inst_1 Bool) (top.res.inst_0 Bool) (top.usr.Delta! Int) (top.usr.OK! Bool) (top.res.init_flag! Bool) (top.res.abs_0! Int) (top.res.abs_1! Bool) (top.res.abs_2! Bool) (top.res.inst_1! Bool) (top.res.inst_0! Bool)) Bool
    (and (= top.res.abs_1! (and (<= (- 1) top.usr.Delta!) (<= top.usr.Delta! 1))) (let ((X1 top.res.abs_0!)) (and (= top.usr.OK! (=> top.res.abs_2! (and (<= 0 X1) (<= X1 20)))) (__node_trans_Store_0 top.usr.Delta! top.res.abs_0! top.res.inst_1! top.usr.Delta top.res.abs_0 top.res.inst_1) (__node_trans_Sofar_0 top.res.abs_1! top.res.abs_2! top.res.inst_0! top.res.abs_1 top.res.abs_2 top.res.inst_0) (not top.res.init_flag!)))))
(define-fun prop ((top.usr.Delta Int) (top.usr.OK Bool) (top.res.init_flag Bool) (top.res.abs_0 Int) (top.res.abs_1 Bool) (top.res.abs_2 Bool) (top.res.inst_1 Bool) (top.res.inst_0 Bool)) Bool
    top.usr.OK)

(inv-constraint str_invariant init trans prop)

(check-synth)

