(set-logic ALIA)

(synth-inv inv_fun ((x (Array Int Int)) (x_length Int) (sum Int) (y Int) (n Int)))


(declare-primed-var x (Array Int Int))
(declare-primed-var x_length Int)
(declare-primed-var sum Int)
(declare-primed-var y Int)
(declare-primed-var n Int)



(define-fun pre_fun ((x (Array Int Int)) (x_length Int) (sum Int) (y Int) (n Int)) Bool
  (and (> n 0)
       (= sum 0)
       (= y 0)
       (> x_length 0)
       (forall ((i Int)) (=> (and (>= i 0) (< i n)) (and (<= 0 i) (< i x_length) (= i (select x i)))))))

(define-fun trans_fun ((x (Array Int Int)) (x_length Int) (sum Int) (y Int) (n Int) (x! (Array Int Int)) (x_length! Int) (sum! Int) (y! Int) (n! Int)) Bool
  (and (= n! n)
       (= x! x)
       (< y n)
       (= y! (+ y 1))
       (= x_length! x_length)
       (<= 0 y)
       (< y x_length)
       (= sum! (+ sum (select x y)))))


(define-fun post_fun ((x (Array Int Int)) (x_length Int) (sum Int) (y Int) (n Int)) Bool
  (or (and (< y n) (<= 0 y) (< y x_length))
      (= (* 2 sum) (* n (+ n 1)))))


(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)