(set-logic LIA)

(synth-inv InvF ((in Int) (inlen Int) (bufferlen Int) (buf Int) (buflim Int)))

(define-fun PreF ((in Int) (inlen Int) (bufferlen Int) (buf Int) (buflim Int)) Bool
    (and (> bufferlen 1) (> inlen 0) (< bufferlen inlen) (= buf 0) (= in 0) (= buflim (- bufferlen 2))))
(define-fun TransF ((in Int) (inlen Int) (bufferlen Int) (buf Int) (buflim Int) (in! Int) (inlen! Int) (bufferlen! Int) (buf! Int) (buflim! Int)) Bool
    (and (not (= buf buflim)) (= buf! (+ buf 1)) (= in! (+ in 1)) (= inlen! inlen) (= bufferlen! bufferlen) (= buflim! buflim)))
(define-fun PostF ((in Int) (inlen Int) (bufferlen Int) (buf Int) (buflim Int)) Bool
    (or (= buf buflim) (and (<= 0 buf) (< buf bufferlen))))

(inv-constraint InvF PreF TransF PostF)

(check-synth)

