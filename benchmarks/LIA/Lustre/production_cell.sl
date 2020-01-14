(set-logic LIA)

(define-fun __node_init_sustain_0 ((sustain.usr.on_a_0 Bool) (sustain.usr.off_a_0 Bool) (sustain.usr.s_a_0 Bool) (sustain.res.init_flag_a_0 Bool)) Bool
    (and (= sustain.usr.s_a_0 sustain.usr.on_a_0) sustain.res.init_flag_a_0))
(define-fun __node_trans_sustain_0 ((sustain.usr.on_a_1 Bool) (sustain.usr.off_a_1 Bool) (sustain.usr.s_a_1 Bool) (sustain.res.init_flag_a_1 Bool) (sustain.usr.on_a_0 Bool) (sustain.usr.off_a_0 Bool) (sustain.usr.s_a_0 Bool) (sustain.res.init_flag_a_0 Bool)) Bool
    (and (= sustain.usr.s_a_1 (ite sustain.usr.on_a_1 true (ite sustain.usr.off_a_1 false sustain.usr.s_a_0))) (not sustain.res.init_flag_a_1)))
(define-fun __node_init_redge_0 ((redge.usr.signal_a_0 Bool) (redge.usr.r_a_0 Bool) (redge.res.init_flag_a_0 Bool) (redge.res.abs_0_a_0 Bool)) Bool
    (and (= redge.usr.r_a_0 redge.usr.signal_a_0) (= redge.res.abs_0_a_0 (not redge.usr.signal_a_0)) redge.res.init_flag_a_0))
(define-fun __node_trans_redge_0 ((redge.usr.signal_a_1 Bool) (redge.usr.r_a_1 Bool) (redge.res.init_flag_a_1 Bool) (redge.res.abs_0_a_1 Bool) (redge.usr.signal_a_0 Bool) (redge.usr.r_a_0 Bool) (redge.res.init_flag_a_0 Bool) (redge.res.abs_0_a_0 Bool)) Bool
    (and (= redge.usr.r_a_1 (and redge.usr.signal_a_1 redge.res.abs_0_a_0)) (= redge.res.abs_0_a_1 (not redge.usr.signal_a_1)) (not redge.res.init_flag_a_1)))
(define-fun __node_init_fedge_0 ((fedge.usr.signal_a_0 Bool) (fedge.usr.f_a_0 Bool) (fedge.res.init_flag_a_0 Bool) (fedge.res.abs_0_a_0 Bool) (fedge.res.abs_1_a_0 Bool) (fedge.res.inst_1_a_0 Bool) (fedge.res.inst_0_a_0 Bool)) Bool
    (and (= fedge.res.abs_0_a_0 (not fedge.usr.signal_a_0)) (= fedge.usr.f_a_0 fedge.res.abs_1_a_0) (__node_init_redge_0 fedge.res.abs_0_a_0 fedge.res.abs_1_a_0 fedge.res.inst_1_a_0 fedge.res.inst_0_a_0) fedge.res.init_flag_a_0))
(define-fun __node_trans_fedge_0 ((fedge.usr.signal_a_1 Bool) (fedge.usr.f_a_1 Bool) (fedge.res.init_flag_a_1 Bool) (fedge.res.abs_0_a_1 Bool) (fedge.res.abs_1_a_1 Bool) (fedge.res.inst_1_a_1 Bool) (fedge.res.inst_0_a_1 Bool) (fedge.usr.signal_a_0 Bool) (fedge.usr.f_a_0 Bool) (fedge.res.init_flag_a_0 Bool) (fedge.res.abs_0_a_0 Bool) (fedge.res.abs_1_a_0 Bool) (fedge.res.inst_1_a_0 Bool) (fedge.res.inst_0_a_0 Bool)) Bool
    (and (= fedge.res.abs_0_a_1 (not fedge.usr.signal_a_1)) (= fedge.usr.f_a_1 fedge.res.abs_1_a_1) (__node_trans_redge_0 fedge.res.abs_0_a_1 fedge.res.abs_1_a_1 fedge.res.inst_1_a_1 fedge.res.inst_0_a_1 fedge.res.abs_0_a_0 fedge.res.abs_1_a_0 fedge.res.inst_1_a_0 fedge.res.inst_0_a_0) (not fedge.res.init_flag_a_1)))
(define-fun __node_init_top_0 ((top.usr.MaySafelyMove_a_0 Bool) (top.usr.TryToMove1_a_0 Bool) (top.usr.TryToMove2_a_0 Bool) (top.usr.OK_a_0 Bool) (top.res.init_flag_a_0 Bool) (top.impl.usr.MayMove1_a_0 Bool) (top.impl.usr.MayMove2_a_0 Bool) (top.impl.usr.stop_a_0 Bool) (top.res.abs_0_a_0 Bool) (top.res.abs_1_a_0 Bool) (top.res.abs_2_a_0 Bool) (top.res.abs_3_a_0 Bool) (top.res.abs_4_a_0 Bool) (top.res.abs_5_a_0 Bool) (top.res.abs_6_a_0 Bool) (top.res.abs_7_a_0 Bool) (top.res.abs_8_a_0 Bool) (top.res.abs_9_a_0 Bool) (top.res.abs_10_a_0 Bool) (top.res.abs_11_a_0 Bool) (top.res.inst_18_a_0 Bool) (top.res.inst_17_a_0 Bool) (top.res.inst_16_a_0 Bool) (top.res.inst_15_a_0 Bool) (top.res.inst_14_a_0 Bool) (top.res.inst_13_a_0 Bool) (top.res.inst_12_a_0 Bool) (top.res.inst_11_a_0 Bool) (top.res.inst_10_a_0 Bool) (top.res.inst_9_a_0 Bool) (top.res.inst_8_a_0 Bool) (top.res.inst_7_a_0 Bool) (top.res.inst_6_a_0 Bool) (top.res.inst_5_a_0 Bool) (top.res.inst_4_a_0 Bool) (top.res.inst_3_a_0 Bool) (top.res.inst_2_a_0 Bool) (top.res.inst_1_a_0 Bool) (top.res.inst_0_a_0 Bool)) Bool
    (and (= top.usr.OK_a_0 true) (= top.impl.usr.MayMove1_a_0 (and top.usr.TryToMove1_a_0 top.usr.MaySafelyMove_a_0)) (= top.res.abs_3_a_0 top.impl.usr.MayMove1_a_0) (let ((X1 top.res.abs_4_a_0)) (and (= top.res.abs_2_a_0 (not top.usr.TryToMove2_a_0)) (= top.impl.usr.MayMove2_a_0 (and top.usr.TryToMove2_a_0 top.usr.MaySafelyMove_a_0)) (= top.res.abs_6_a_0 top.impl.usr.MayMove2_a_0) (let ((X2 top.res.abs_7_a_0)) (and (= top.res.abs_5_a_0 (not top.usr.TryToMove1_a_0)) (= top.impl.usr.stop_a_0 (or top.res.abs_8_a_0 top.res.abs_9_a_0)) (= top.res.abs_0_a_0 (or X1 X2)) (let ((X3 top.res.abs_1_a_0)) (and (__node_init_redge_0 top.res.abs_3_a_0 top.res.abs_4_a_0 top.res.inst_18_a_0 top.res.inst_17_a_0) (__node_init_redge_0 top.res.abs_6_a_0 top.res.abs_7_a_0 top.res.inst_16_a_0 top.res.inst_15_a_0) (__node_init_fedge_0 top.impl.usr.MayMove1_a_0 top.res.abs_8_a_0 top.res.inst_14_a_0 top.res.inst_13_a_0 top.res.inst_12_a_0 top.res.inst_11_a_0 top.res.inst_10_a_0) (__node_init_fedge_0 top.impl.usr.MayMove2_a_0 top.res.abs_9_a_0 top.res.inst_9_a_0 top.res.inst_8_a_0 top.res.inst_7_a_0 top.res.inst_6_a_0 top.res.inst_5_a_0) (__node_init_sustain_0 top.res.abs_0_a_0 top.impl.usr.stop_a_0 top.res.abs_1_a_0 top.res.inst_4_a_0) (__node_init_redge_0 top.usr.TryToMove1_a_0 top.res.abs_10_a_0 top.res.inst_3_a_0 top.res.inst_2_a_0) (__node_init_redge_0 top.usr.TryToMove2_a_0 top.res.abs_11_a_0 top.res.inst_1_a_0 top.res.inst_0_a_0) top.res.init_flag_a_0))))))))
(define-fun __node_trans_top_0 ((top.usr.MaySafelyMove_a_1 Bool) (top.usr.TryToMove1_a_1 Bool) (top.usr.TryToMove2_a_1 Bool) (top.usr.OK_a_1 Bool) (top.res.init_flag_a_1 Bool) (top.impl.usr.MayMove1_a_1 Bool) (top.impl.usr.MayMove2_a_1 Bool) (top.impl.usr.stop_a_1 Bool) (top.res.abs_0_a_1 Bool) (top.res.abs_1_a_1 Bool) (top.res.abs_2_a_1 Bool) (top.res.abs_3_a_1 Bool) (top.res.abs_4_a_1 Bool) (top.res.abs_5_a_1 Bool) (top.res.abs_6_a_1 Bool) (top.res.abs_7_a_1 Bool) (top.res.abs_8_a_1 Bool) (top.res.abs_9_a_1 Bool) (top.res.abs_10_a_1 Bool) (top.res.abs_11_a_1 Bool) (top.res.inst_18_a_1 Bool) (top.res.inst_17_a_1 Bool) (top.res.inst_16_a_1 Bool) (top.res.inst_15_a_1 Bool) (top.res.inst_14_a_1 Bool) (top.res.inst_13_a_1 Bool) (top.res.inst_12_a_1 Bool) (top.res.inst_11_a_1 Bool) (top.res.inst_10_a_1 Bool) (top.res.inst_9_a_1 Bool) (top.res.inst_8_a_1 Bool) (top.res.inst_7_a_1 Bool) (top.res.inst_6_a_1 Bool) (top.res.inst_5_a_1 Bool) (top.res.inst_4_a_1 Bool) (top.res.inst_3_a_1 Bool) (top.res.inst_2_a_1 Bool) (top.res.inst_1_a_1 Bool) (top.res.inst_0_a_1 Bool) (top.usr.MaySafelyMove_a_0 Bool) (top.usr.TryToMove1_a_0 Bool) (top.usr.TryToMove2_a_0 Bool) (top.usr.OK_a_0 Bool) (top.res.init_flag_a_0 Bool) (top.impl.usr.MayMove1_a_0 Bool) (top.impl.usr.MayMove2_a_0 Bool) (top.impl.usr.stop_a_0 Bool) (top.res.abs_0_a_0 Bool) (top.res.abs_1_a_0 Bool) (top.res.abs_2_a_0 Bool) (top.res.abs_3_a_0 Bool) (top.res.abs_4_a_0 Bool) (top.res.abs_5_a_0 Bool) (top.res.abs_6_a_0 Bool) (top.res.abs_7_a_0 Bool) (top.res.abs_8_a_0 Bool) (top.res.abs_9_a_0 Bool) (top.res.abs_10_a_0 Bool) (top.res.abs_11_a_0 Bool) (top.res.inst_18_a_0 Bool) (top.res.inst_17_a_0 Bool) (top.res.inst_16_a_0 Bool) (top.res.inst_15_a_0 Bool) (top.res.inst_14_a_0 Bool) (top.res.inst_13_a_0 Bool) (top.res.inst_12_a_0 Bool) (top.res.inst_11_a_0 Bool) (top.res.inst_10_a_0 Bool) (top.res.inst_9_a_0 Bool) (top.res.inst_8_a_0 Bool) (top.res.inst_7_a_0 Bool) (top.res.inst_6_a_0 Bool) (top.res.inst_5_a_0 Bool) (top.res.inst_4_a_0 Bool) (top.res.inst_3_a_0 Bool) (top.res.inst_2_a_0 Bool) (top.res.inst_1_a_0 Bool) (top.res.inst_0_a_0 Bool)) Bool
    (and (= top.impl.usr.MayMove2_a_1 (and top.usr.TryToMove2_a_1 top.usr.MaySafelyMove_a_1)) (= top.impl.usr.MayMove1_a_1 (and top.usr.TryToMove1_a_1 top.usr.MaySafelyMove_a_1)) (= top.res.abs_6_a_1 (and top.impl.usr.MayMove2_a_1 top.res.abs_5_a_0)) (= top.res.abs_3_a_1 (and top.impl.usr.MayMove1_a_1 top.res.abs_2_a_0)) (let ((X1 top.res.abs_7_a_1)) (let ((X2 top.res.abs_4_a_1)) (and (= top.res.abs_0_a_1 (or X2 X1)) (= top.impl.usr.stop_a_1 (or top.res.abs_8_a_1 top.res.abs_9_a_1)) (let ((X3 top.res.abs_1_a_1)) (and (= top.usr.OK_a_1 (ite (or (not top.res.abs_10_a_1) (not top.res.abs_11_a_1)) (and (and (or (or (and (not X2) (not X1)) (and (not X1) (not top.impl.usr.stop_a_1))) (and (not X2) (not top.impl.usr.stop_a_1))) (not (and (and X2 X1) top.impl.usr.stop_a_1))) (ite X3 top.usr.MaySafelyMove_a_1 true)) true)) (= top.res.abs_2_a_1 (not top.usr.TryToMove2_a_1)) (= top.res.abs_5_a_1 (not top.usr.TryToMove1_a_1)) (__node_trans_redge_0 top.res.abs_3_a_1 top.res.abs_4_a_1 top.res.inst_18_a_1 top.res.inst_17_a_1 top.res.abs_3_a_0 top.res.abs_4_a_0 top.res.inst_18_a_0 top.res.inst_17_a_0) (__node_trans_redge_0 top.res.abs_6_a_1 top.res.abs_7_a_1 top.res.inst_16_a_1 top.res.inst_15_a_1 top.res.abs_6_a_0 top.res.abs_7_a_0 top.res.inst_16_a_0 top.res.inst_15_a_0) (__node_trans_fedge_0 top.impl.usr.MayMove1_a_1 top.res.abs_8_a_1 top.res.inst_14_a_1 top.res.inst_13_a_1 top.res.inst_12_a_1 top.res.inst_11_a_1 top.res.inst_10_a_1 top.impl.usr.MayMove1_a_0 top.res.abs_8_a_0 top.res.inst_14_a_0 top.res.inst_13_a_0 top.res.inst_12_a_0 top.res.inst_11_a_0 top.res.inst_10_a_0) (__node_trans_fedge_0 top.impl.usr.MayMove2_a_1 top.res.abs_9_a_1 top.res.inst_9_a_1 top.res.inst_8_a_1 top.res.inst_7_a_1 top.res.inst_6_a_1 top.res.inst_5_a_1 top.impl.usr.MayMove2_a_0 top.res.abs_9_a_0 top.res.inst_9_a_0 top.res.inst_8_a_0 top.res.inst_7_a_0 top.res.inst_6_a_0 top.res.inst_5_a_0) (__node_trans_sustain_0 top.res.abs_0_a_1 top.impl.usr.stop_a_1 top.res.abs_1_a_1 top.res.inst_4_a_1 top.res.abs_0_a_0 top.impl.usr.stop_a_0 top.res.abs_1_a_0 top.res.inst_4_a_0) (__node_trans_redge_0 top.usr.TryToMove1_a_1 top.res.abs_10_a_1 top.res.inst_3_a_1 top.res.inst_2_a_1 top.usr.TryToMove1_a_0 top.res.abs_10_a_0 top.res.inst_3_a_0 top.res.inst_2_a_0) (__node_trans_redge_0 top.usr.TryToMove2_a_1 top.res.abs_11_a_1 top.res.inst_1_a_1 top.res.inst_0_a_1 top.usr.TryToMove2_a_0 top.res.abs_11_a_0 top.res.inst_1_a_0 top.res.inst_0_a_0) (not top.res.init_flag_a_1))))))))
(synth-inv str_invariant ((top.usr.MaySafelyMove Bool) (top.usr.TryToMove1 Bool) (top.usr.TryToMove2 Bool) (top.usr.OK Bool) (top.res.init_flag Bool) (top.impl.usr.MayMove1 Bool) (top.impl.usr.MayMove2 Bool) (top.impl.usr.stop Bool) (top.res.abs_0 Bool) (top.res.abs_1 Bool) (top.res.abs_2 Bool) (top.res.abs_3 Bool) (top.res.abs_4 Bool) (top.res.abs_5 Bool) (top.res.abs_6 Bool) (top.res.abs_7 Bool) (top.res.abs_8 Bool) (top.res.abs_9 Bool) (top.res.abs_10 Bool) (top.res.abs_11 Bool) (top.res.inst_18 Bool) (top.res.inst_17 Bool) (top.res.inst_16 Bool) (top.res.inst_15 Bool) (top.res.inst_14 Bool) (top.res.inst_13 Bool) (top.res.inst_12 Bool) (top.res.inst_11 Bool) (top.res.inst_10 Bool) (top.res.inst_9 Bool) (top.res.inst_8 Bool) (top.res.inst_7 Bool) (top.res.inst_6 Bool) (top.res.inst_5 Bool) (top.res.inst_4 Bool) (top.res.inst_3 Bool) (top.res.inst_2 Bool) (top.res.inst_1 Bool) (top.res.inst_0 Bool)))

(define-fun init ((top.usr.MaySafelyMove Bool) (top.usr.TryToMove1 Bool) (top.usr.TryToMove2 Bool) (top.usr.OK Bool) (top.res.init_flag Bool) (top.impl.usr.MayMove1 Bool) (top.impl.usr.MayMove2 Bool) (top.impl.usr.stop Bool) (top.res.abs_0 Bool) (top.res.abs_1 Bool) (top.res.abs_2 Bool) (top.res.abs_3 Bool) (top.res.abs_4 Bool) (top.res.abs_5 Bool) (top.res.abs_6 Bool) (top.res.abs_7 Bool) (top.res.abs_8 Bool) (top.res.abs_9 Bool) (top.res.abs_10 Bool) (top.res.abs_11 Bool) (top.res.inst_18 Bool) (top.res.inst_17 Bool) (top.res.inst_16 Bool) (top.res.inst_15 Bool) (top.res.inst_14 Bool) (top.res.inst_13 Bool) (top.res.inst_12 Bool) (top.res.inst_11 Bool) (top.res.inst_10 Bool) (top.res.inst_9 Bool) (top.res.inst_8 Bool) (top.res.inst_7 Bool) (top.res.inst_6 Bool) (top.res.inst_5 Bool) (top.res.inst_4 Bool) (top.res.inst_3 Bool) (top.res.inst_2 Bool) (top.res.inst_1 Bool) (top.res.inst_0 Bool)) Bool
    (and (= top.usr.OK true) (= top.impl.usr.MayMove1 (and top.usr.TryToMove1 top.usr.MaySafelyMove)) (= top.res.abs_3 top.impl.usr.MayMove1) (let ((X1 top.res.abs_4)) (and (= top.res.abs_2 (not top.usr.TryToMove2)) (= top.impl.usr.MayMove2 (and top.usr.TryToMove2 top.usr.MaySafelyMove)) (= top.res.abs_6 top.impl.usr.MayMove2) (let ((X2 top.res.abs_7)) (and (= top.res.abs_5 (not top.usr.TryToMove1)) (= top.impl.usr.stop (or top.res.abs_8 top.res.abs_9)) (= top.res.abs_0 (or X1 X2)) (let ((X3 top.res.abs_1)) (and (__node_init_redge_0 top.res.abs_3 top.res.abs_4 top.res.inst_18 top.res.inst_17) (__node_init_redge_0 top.res.abs_6 top.res.abs_7 top.res.inst_16 top.res.inst_15) (__node_init_fedge_0 top.impl.usr.MayMove1 top.res.abs_8 top.res.inst_14 top.res.inst_13 top.res.inst_12 top.res.inst_11 top.res.inst_10) (__node_init_fedge_0 top.impl.usr.MayMove2 top.res.abs_9 top.res.inst_9 top.res.inst_8 top.res.inst_7 top.res.inst_6 top.res.inst_5) (__node_init_sustain_0 top.res.abs_0 top.impl.usr.stop top.res.abs_1 top.res.inst_4) (__node_init_redge_0 top.usr.TryToMove1 top.res.abs_10 top.res.inst_3 top.res.inst_2) (__node_init_redge_0 top.usr.TryToMove2 top.res.abs_11 top.res.inst_1 top.res.inst_0) top.res.init_flag))))))))
(define-fun trans ((top.usr.MaySafelyMove Bool) (top.usr.TryToMove1 Bool) (top.usr.TryToMove2 Bool) (top.usr.OK Bool) (top.res.init_flag Bool) (top.impl.usr.MayMove1 Bool) (top.impl.usr.MayMove2 Bool) (top.impl.usr.stop Bool) (top.res.abs_0 Bool) (top.res.abs_1 Bool) (top.res.abs_2 Bool) (top.res.abs_3 Bool) (top.res.abs_4 Bool) (top.res.abs_5 Bool) (top.res.abs_6 Bool) (top.res.abs_7 Bool) (top.res.abs_8 Bool) (top.res.abs_9 Bool) (top.res.abs_10 Bool) (top.res.abs_11 Bool) (top.res.inst_18 Bool) (top.res.inst_17 Bool) (top.res.inst_16 Bool) (top.res.inst_15 Bool) (top.res.inst_14 Bool) (top.res.inst_13 Bool) (top.res.inst_12 Bool) (top.res.inst_11 Bool) (top.res.inst_10 Bool) (top.res.inst_9 Bool) (top.res.inst_8 Bool) (top.res.inst_7 Bool) (top.res.inst_6 Bool) (top.res.inst_5 Bool) (top.res.inst_4 Bool) (top.res.inst_3 Bool) (top.res.inst_2 Bool) (top.res.inst_1 Bool) (top.res.inst_0 Bool) (top.usr.MaySafelyMove! Bool) (top.usr.TryToMove1! Bool) (top.usr.TryToMove2! Bool) (top.usr.OK! Bool) (top.res.init_flag! Bool) (top.impl.usr.MayMove1! Bool) (top.impl.usr.MayMove2! Bool) (top.impl.usr.stop! Bool) (top.res.abs_0! Bool) (top.res.abs_1! Bool) (top.res.abs_2! Bool) (top.res.abs_3! Bool) (top.res.abs_4! Bool) (top.res.abs_5! Bool) (top.res.abs_6! Bool) (top.res.abs_7! Bool) (top.res.abs_8! Bool) (top.res.abs_9! Bool) (top.res.abs_10! Bool) (top.res.abs_11! Bool) (top.res.inst_18! Bool) (top.res.inst_17! Bool) (top.res.inst_16! Bool) (top.res.inst_15! Bool) (top.res.inst_14! Bool) (top.res.inst_13! Bool) (top.res.inst_12! Bool) (top.res.inst_11! Bool) (top.res.inst_10! Bool) (top.res.inst_9! Bool) (top.res.inst_8! Bool) (top.res.inst_7! Bool) (top.res.inst_6! Bool) (top.res.inst_5! Bool) (top.res.inst_4! Bool) (top.res.inst_3! Bool) (top.res.inst_2! Bool) (top.res.inst_1! Bool) (top.res.inst_0! Bool)) Bool
    (and (= top.impl.usr.MayMove2! (and top.usr.TryToMove2! top.usr.MaySafelyMove!)) (= top.impl.usr.MayMove1! (and top.usr.TryToMove1! top.usr.MaySafelyMove!)) (= top.res.abs_6! (and top.impl.usr.MayMove2! top.res.abs_5)) (= top.res.abs_3! (and top.impl.usr.MayMove1! top.res.abs_2)) (let ((X1 top.res.abs_7!)) (let ((X2 top.res.abs_4!)) (and (= top.res.abs_0! (or X2 X1)) (= top.impl.usr.stop! (or top.res.abs_8! top.res.abs_9!)) (let ((X3 top.res.abs_1!)) (and (= top.usr.OK! (ite (or (not top.res.abs_10!) (not top.res.abs_11!)) (and (and (or (or (and (not X2) (not X1)) (and (not X1) (not top.impl.usr.stop!))) (and (not X2) (not top.impl.usr.stop!))) (not (and (and X2 X1) top.impl.usr.stop!))) (ite X3 top.usr.MaySafelyMove! true)) true)) (= top.res.abs_2! (not top.usr.TryToMove2!)) (= top.res.abs_5! (not top.usr.TryToMove1!)) (__node_trans_redge_0 top.res.abs_3! top.res.abs_4! top.res.inst_18! top.res.inst_17! top.res.abs_3 top.res.abs_4 top.res.inst_18 top.res.inst_17) (__node_trans_redge_0 top.res.abs_6! top.res.abs_7! top.res.inst_16! top.res.inst_15! top.res.abs_6 top.res.abs_7 top.res.inst_16 top.res.inst_15) (__node_trans_fedge_0 top.impl.usr.MayMove1! top.res.abs_8! top.res.inst_14! top.res.inst_13! top.res.inst_12! top.res.inst_11! top.res.inst_10! top.impl.usr.MayMove1 top.res.abs_8 top.res.inst_14 top.res.inst_13 top.res.inst_12 top.res.inst_11 top.res.inst_10) (__node_trans_fedge_0 top.impl.usr.MayMove2! top.res.abs_9! top.res.inst_9! top.res.inst_8! top.res.inst_7! top.res.inst_6! top.res.inst_5! top.impl.usr.MayMove2 top.res.abs_9 top.res.inst_9 top.res.inst_8 top.res.inst_7 top.res.inst_6 top.res.inst_5) (__node_trans_sustain_0 top.res.abs_0! top.impl.usr.stop! top.res.abs_1! top.res.inst_4! top.res.abs_0 top.impl.usr.stop top.res.abs_1 top.res.inst_4) (__node_trans_redge_0 top.usr.TryToMove1! top.res.abs_10! top.res.inst_3! top.res.inst_2! top.usr.TryToMove1 top.res.abs_10 top.res.inst_3 top.res.inst_2) (__node_trans_redge_0 top.usr.TryToMove2! top.res.abs_11! top.res.inst_1! top.res.inst_0! top.usr.TryToMove2 top.res.abs_11 top.res.inst_1 top.res.inst_0) (not top.res.init_flag!))))))))
(define-fun prop ((top.usr.MaySafelyMove Bool) (top.usr.TryToMove1 Bool) (top.usr.TryToMove2 Bool) (top.usr.OK Bool) (top.res.init_flag Bool) (top.impl.usr.MayMove1 Bool) (top.impl.usr.MayMove2 Bool) (top.impl.usr.stop Bool) (top.res.abs_0 Bool) (top.res.abs_1 Bool) (top.res.abs_2 Bool) (top.res.abs_3 Bool) (top.res.abs_4 Bool) (top.res.abs_5 Bool) (top.res.abs_6 Bool) (top.res.abs_7 Bool) (top.res.abs_8 Bool) (top.res.abs_9 Bool) (top.res.abs_10 Bool) (top.res.abs_11 Bool) (top.res.inst_18 Bool) (top.res.inst_17 Bool) (top.res.inst_16 Bool) (top.res.inst_15 Bool) (top.res.inst_14 Bool) (top.res.inst_13 Bool) (top.res.inst_12 Bool) (top.res.inst_11 Bool) (top.res.inst_10 Bool) (top.res.inst_9 Bool) (top.res.inst_8 Bool) (top.res.inst_7 Bool) (top.res.inst_6 Bool) (top.res.inst_5 Bool) (top.res.inst_4 Bool) (top.res.inst_3 Bool) (top.res.inst_2 Bool) (top.res.inst_1 Bool) (top.res.inst_0 Bool)) Bool
    top.usr.OK)

(inv-constraint str_invariant init trans prop)

(check-synth)

