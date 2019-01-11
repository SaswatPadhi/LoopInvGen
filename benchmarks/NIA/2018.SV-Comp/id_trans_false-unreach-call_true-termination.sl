(set-logic NIA)

(synth-inv InvF ((j Int) (k Int) (idBitLength Int) (materialLength Int) (nlen Int)))

(declare-primed-var j Int)
(declare-primed-var k Int)
(declare-primed-var idBitLength Int)
(declare-primed-var materialLength Int)
(declare-primed-var nlen Int)

(define-fun PreF ((j Int) (k Int) (idBitLength Int) (materialLength Int) (nlen Int)) Bool
   (and (= j 0) (= nlen (/ idBitLength 32))))

(define-fun TransF ((j Int) (k Int) (idBitLength Int) (materialLength Int) (nlen Int)
    (j! Int) (k! Int) (idBitLength! Int) (materialLength! Int) (nlen! Int)) Bool
   (and (< j (/ idBitLength 8)) 
  (< j materialLength)
  (= j! (+ j 1))
  (= materialLength! materialLength)
  (= idBitLength! idBitLength)
  (= nlen! nlen)
  ))

(define-fun PostF ((j Int) (k Int) (idBitLength Int) (materialLength Int) (nlen Int)) Bool
   (or (and (< j (/ idBitLength 8)) (< j materialLength))
  (and (<= 0 j)
    (< j materialLength)
    (<= 0 (/ j 4))
    (< (/ j 4) nlen)) 
  ))

(inv-constraint InvF PreF TransF PostF)

(check-synth)

