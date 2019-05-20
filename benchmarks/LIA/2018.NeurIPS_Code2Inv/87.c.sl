(set-logic LIA)

( declare-primed-var lock Int )
( declare-primed-var x Int )
( declare-primed-var y Int )
( declare-primed-var tmp Int )

( declare-primed-var lock_0 Int )
( declare-primed-var lock_1 Int )
( declare-primed-var lock_2 Int )
( declare-primed-var lock_3 Int )
( declare-primed-var lock_4 Int )
( declare-primed-var lock_5 Int )
( declare-primed-var x_0 Int )
( declare-primed-var x_1 Int )
( declare-primed-var x_2 Int )
( declare-primed-var x_3 Int )
( declare-primed-var x_4 Int )
( declare-primed-var x_5 Int )
( declare-primed-var y_0 Int )
( declare-primed-var y_1 Int )
( declare-primed-var y_2 Int )
( declare-primed-var y_3 Int )

( synth-inv inv-f( ( lock Int )( x Int )( y Int )( tmp Int )( lock_0 Int )( lock_1 Int )( lock_2 Int )( lock_3 Int )( lock_4 Int )( lock_5 Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( x_4 Int )( x_5 Int )( y_0 Int )( y_1 Int )( y_2 Int )( y_3 Int ) ) )

( define-fun pre-f ( ( lock Int )( x Int )( y Int )( tmp Int )( lock_0 Int )( lock_1 Int )( lock_2 Int )( lock_3 Int )( lock_4 Int )( lock_5 Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( x_4 Int )( x_5 Int )( y_0 Int )( y_1 Int )( y_2 Int )( y_3 Int ) ) Bool
	( and
		( = lock lock_1 )
		( = x x_1 )
		( = y y_0 )
		( = x_1 y_0 )
		( = lock_1 1 )
	)
)

( define-fun trans-f ( ( lock Int )( x Int )( y Int )( tmp Int )( lock_0 Int )( lock_1 Int )( lock_2 Int )( lock_3 Int )( lock_4 Int )( lock_5 Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( x_4 Int )( x_5 Int )( y_0 Int )( y_1 Int )( y_2 Int )( y_3 Int )( lock! Int )( x! Int )( y! Int )( tmp! Int )( lock_0! Int )( lock_1! Int )( lock_2! Int )( lock_3! Int )( lock_4! Int )( lock_5! Int )( x_0! Int )( x_1! Int )( x_2! Int )( x_3! Int )( x_4! Int )( x_5! Int )( y_0! Int )( y_1! Int )( y_2! Int )( y_3! Int ) ) Bool
	( or
		( and
			( = lock_2 lock )
			( = x_2 x )
			( = y_1 y )
			( = lock_2 lock! )
			( = x_2 x! )
			( = y_1 y! )
			( = lock lock! )
			(= tmp tmp! )
		)
		( and
			( = lock_2 lock )
			( = x_2 x )
			( = y_1 y )
			( not ( = x_2 y_1 ) )
			( = lock_3 1 )
			( = x_3 y_1 )
			( = lock_4 lock_3 )
			( = x_4 x_3 )
			( = y_2 y_1 )
			( = lock_4 lock! )
			( = x_4 x! )
			( = y_2 y! )
			(= tmp tmp! )
		)
		( and
			( = lock_2 lock )
			( = x_2 x )
			( = y_1 y )
			( not ( = x_2 y_1 ) )
			( = lock_5 0 )
			( = x_5 y_1 )
			( = y_3 ( + y_1 1 ) )
			( = lock_4 lock_5 )
			( = x_4 x_5 )
			( = y_2 y_3 )
			( = lock_4 lock! )
			( = x_4 x! )
			( = y_2 y! )
			(= tmp tmp! )
		)
	)
)

( define-fun post-f ( ( lock Int )( x Int )( y Int )( tmp Int )( lock_0 Int )( lock_1 Int )( lock_2 Int )( lock_3 Int )( lock_4 Int )( lock_5 Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( x_4 Int )( x_5 Int )( y_0 Int )( y_1 Int )( y_2 Int )( y_3 Int ) ) Bool
	( or
		( not
			( and
				( = lock lock_2)
				( = x x_2)
				( = y y_1)
			)
		)
		( not
			( and
				( not ( not ( = x_2 y_1 ) ) )
				( not ( = lock_2 1 ) )
			)
		)
	)
)

( inv-constraint inv-f pre-f trans-f post-f )
( check-synth )
