(set-logic LIA)

(synth-inv InvF ((i Int) (k Int)))

(declare-primed-var i Int)
(declare-primed-var k Int)

(define-fun PreF ((i Int) (k Int)) Bool
   (and (= i 0) 
	(<= 0 k)
	(<= k 10)))

(define-fun TransF ((i Int) (k Int) 
			(i! Int) (k! Int)) Bool
   (and (< i (* 1000000 k)) 
	(= i! (+ i k)) 
	(= k! k)))

(define-fun PostF ((i Int) (k Int)) Bool
   (or (< i (* 1000000 k)) 
	(= i (* 1000000 k))))

(inv-constraint InvF PreF TransF PostF)

(check-synth)
