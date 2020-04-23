(set-logic LIA)

(synth-inv InvF ((MAXPATHLEN Int) (pathbuf_off Int) (bound_off Int) (glob2_p_off Int) (glob2_pathbuf_off Int) (glob2_pathlim_off Int)))

(define-fun PreF ((MAXPATHLEN Int) (pathbuf_off Int) (bound_off Int) (glob2_p_off Int) (glob2_pathbuf_off Int) (glob2_pathlim_off Int)) Bool
    (and (> MAXPATHLEN 0) (< MAXPATHLEN 2147483647) (= pathbuf_off 0) (= bound_off (- (+ pathbuf_off (+ MAXPATHLEN 1)) 1)) (= glob2_pathbuf_off pathbuf_off) (= glob2_pathlim_off bound_off) (= glob2_p_off glob2_pathbuf_off)))
(define-fun TransF ((MAXPATHLEN Int) (pathbuf_off Int) (bound_off Int) (glob2_p_off Int) (glob2_pathbuf_off Int) (glob2_pathlim_off Int) (MAXPATHLEN! Int) (pathbuf_off! Int) (bound_off! Int) (glob2_p_off! Int) (glob2_pathbuf_off! Int) (glob2_pathlim_off! Int)) Bool
    (and (<= glob2_p_off glob2_pathlim_off) (= glob2_p_off (+ glob2_p_off 1)) (= MAXPATHLEN! MAXPATHLEN) (= pathbuf_off! pathbuf_off) (= bound_off! bound_off) (= glob2_pathbuf_off! glob2_pathbuf_off) (= glob2_pathlim_off! glob2_pathlim_off)))
(define-fun PostF ((MAXPATHLEN Int) (pathbuf_off Int) (bound_off Int) (glob2_p_off Int) (glob2_pathbuf_off Int) (glob2_pathlim_off Int)) Bool
    (or (not (<= glob2_p_off glob2_pathlim_off)) (and (<= glob2_p_off 0) (< glob2_p_off (+ MAXPATHLEN 1)))))

(inv-constraint InvF PreF TransF PostF)

(check-synth)

