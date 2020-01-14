(set-logic LIA)

(define-fun __node_init_top_0 ((top.usr.OK_a_0 Bool) (top.res.init_flag_a_0 Bool) (top.impl.usr.a_a_0 Bool) (top.impl.usr.b_a_0 Bool) (top.impl.usr.c_a_0 Bool)) Bool
    (and (= top.impl.usr.c_a_0 false) (= top.impl.usr.b_a_0 false) (= top.impl.usr.a_a_0 true) (= top.usr.OK_a_0 (and (or (or (or (or (not top.impl.usr.a_a_0) (and (not top.impl.usr.b_a_0) top.impl.usr.c_a_0)) (and (and (not top.impl.usr.a_a_0) top.impl.usr.b_a_0) (not top.impl.usr.c_a_0))) (and (and top.impl.usr.a_a_0 (not top.impl.usr.b_a_0)) (not top.impl.usr.c_a_0))) (and (and top.impl.usr.a_a_0 top.impl.usr.b_a_0) top.impl.usr.c_a_0)) (not (and (and top.impl.usr.a_a_0 top.impl.usr.b_a_0) top.impl.usr.c_a_0)))) top.res.init_flag_a_0))
(define-fun __node_trans_top_0 ((top.usr.OK_a_1 Bool) (top.res.init_flag_a_1 Bool) (top.impl.usr.a_a_1 Bool) (top.impl.usr.b_a_1 Bool) (top.impl.usr.c_a_1 Bool) (top.usr.OK_a_0 Bool) (top.res.init_flag_a_0 Bool) (top.impl.usr.a_a_0 Bool) (top.impl.usr.b_a_0 Bool) (top.impl.usr.c_a_0 Bool)) Bool
    (and (= top.impl.usr.c_a_1 top.impl.usr.b_a_0) (= top.impl.usr.b_a_1 top.impl.usr.a_a_0) (= top.impl.usr.a_a_1 top.impl.usr.c_a_0) (= top.usr.OK_a_1 (and (or (or (or (or (not top.impl.usr.a_a_1) (and (not top.impl.usr.b_a_1) top.impl.usr.c_a_1)) (and (and (not top.impl.usr.a_a_1) top.impl.usr.b_a_1) (not top.impl.usr.c_a_1))) (and (and top.impl.usr.a_a_1 (not top.impl.usr.b_a_1)) (not top.impl.usr.c_a_1))) (and (and top.impl.usr.a_a_1 top.impl.usr.b_a_1) top.impl.usr.c_a_1)) (not (and (and top.impl.usr.a_a_1 top.impl.usr.b_a_1) top.impl.usr.c_a_1)))) (not top.res.init_flag_a_1)))
(synth-inv str_invariant ((top.usr.OK Bool) (top.res.init_flag Bool) (top.impl.usr.a Bool) (top.impl.usr.b Bool) (top.impl.usr.c Bool)))

(define-fun init ((top.usr.OK Bool) (top.res.init_flag Bool) (top.impl.usr.a Bool) (top.impl.usr.b Bool) (top.impl.usr.c Bool)) Bool
    (and (= top.impl.usr.c false) (= top.impl.usr.b false) (= top.impl.usr.a true) (= top.usr.OK (and (or (or (or (or (not top.impl.usr.a) (and (not top.impl.usr.b) top.impl.usr.c)) (and (and (not top.impl.usr.a) top.impl.usr.b) (not top.impl.usr.c))) (and (and top.impl.usr.a (not top.impl.usr.b)) (not top.impl.usr.c))) (and (and top.impl.usr.a top.impl.usr.b) top.impl.usr.c)) (not (and (and top.impl.usr.a top.impl.usr.b) top.impl.usr.c)))) top.res.init_flag))
(define-fun trans ((top.usr.OK Bool) (top.res.init_flag Bool) (top.impl.usr.a Bool) (top.impl.usr.b Bool) (top.impl.usr.c Bool) (top.usr.OK! Bool) (top.res.init_flag! Bool) (top.impl.usr.a! Bool) (top.impl.usr.b! Bool) (top.impl.usr.c! Bool)) Bool
    (and (= top.impl.usr.c! top.impl.usr.b) (= top.impl.usr.b! top.impl.usr.a) (= top.impl.usr.a! top.impl.usr.c) (= top.usr.OK! (and (or (or (or (or (not top.impl.usr.a!) (and (not top.impl.usr.b!) top.impl.usr.c!)) (and (and (not top.impl.usr.a!) top.impl.usr.b!) (not top.impl.usr.c!))) (and (and top.impl.usr.a! (not top.impl.usr.b!)) (not top.impl.usr.c!))) (and (and top.impl.usr.a! top.impl.usr.b!) top.impl.usr.c!)) (not (and (and top.impl.usr.a! top.impl.usr.b!) top.impl.usr.c!)))) (not top.res.init_flag!)))
(define-fun prop ((top.usr.OK Bool) (top.res.init_flag Bool) (top.impl.usr.a Bool) (top.impl.usr.b Bool) (top.impl.usr.c Bool)) Bool
    top.usr.OK)

(inv-constraint str_invariant init trans prop)

(check-synth)

