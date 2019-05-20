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
( declare-primed-var y_0 Int )
( declare-primed-var y_1 Int )
( declare-primed-var y_2 Int )
( declare-primed-var y_3 Int )
( declare-primed-var y_4 Int )

( synth-inv inv-f( ( lock Int )( x Int )( y Int )( tmp Int )( lock_0 Int )( lock_1 Int )( lock_2 Int )( lock_3 Int )( lock_4 Int )( lock_5 Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( x_4 Int )( y_0 Int )( y_1 Int )( y_2 Int )( y_3 Int )( y_4 Int ) ) )

( define-fun pre-f ( ( lock Int )( x Int )( y Int )( tmp Int )( lock_0 Int )( lock_1 Int )( lock_2 Int )( lock_3 Int )( lock_4 Int )( lock_5 Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( x_4 Int )( y_0 Int )( y_1 Int )( y_2 Int )( y_3 Int )( y_4 Int ) ) Bool
	( and
		( = lock lock_1 )
		( = x x_0 )
		( = y y_1 )
		( = y_1 ( + x_0 1 ) )
		( = lock_1 0 )
	)
)

( define-fun trans-f ( ( lock Int )( x Int )( y Int )( tmp Int )( lock_0 Int )( lock_1 Int )( lock_2 Int )( lock_3 Int )( lock_4 Int )( lock_5 Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( x_4 Int )( y_0 Int )( y_1 Int )( y_2 Int )( y_3 Int )( y_4 Int )( lock! Int )( x! Int )( y! Int )( tmp! Int )( lock_0! Int )( lock_1! Int )( lock_2! Int )( lock_3! Int )( lock_4! Int )( lock_5! Int )( x_0! Int )( x_1! Int )( x_2! Int )( x_3! Int )( x_4! Int )( y_0! Int )( y_1! Int )( y_2! Int )( y_3! Int )( y_4! Int ) ) Bool
	( or
		( and
			( = lock_2 lock )
			( = x_1 x )
			( = y_2 y )
			( = lock_2 lock! )
			( = x_1 x! )
			( = y_2 y! )
			( = lock lock! )
			(= tmp tmp! )
		)
		( and
			( = lock_2 lock )
			( = x_1 x )
			( = y_2 y )
			( not ( = x_1 y_2 ) )
			( = lock_3 1 )
			( = x_2 y_2 )
			( = lock_4 lock_3 )
			( = x_3 x_2 )
			( = y_3 y_2 )
			( = lock_4 lock! )
			( = x_3 x! )
			( = y_3 y! )
			(= tmp tmp! )
		)
		( and
			( = lock_2 lock )
			( = x_1 x )
			( = y_2 y )
			( not ( = x_1 y_2 ) )
			( = lock_5 0 )
			( = x_4 y_2 )
			( = y_4 ( + y_2 1 ) )
			( = lock_4 lock_5 )
			( = x_3 x_4 )
			( = y_3 y_4 )
			( = lock_4 lock! )
			( = x_3 x! )
			( = y_3 y! )
			(= tmp tmp! )
		)
	)
)

( define-fun post-f ( ( lock Int )( x Int )( y Int )( tmp Int )( lock_0 Int )( lock_1 Int )( lock_2 Int )( lock_3 Int )( lock_4 Int )( lock_5 Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( x_4 Int )( y_0 Int )( y_1 Int )( y_2 Int )( y_3 Int )( y_4 Int ) ) Bool
	( or
		( not
			( and
				( = lock lock_2)
				( = x x_1)
				( = y y_2)
			)
		)
		( not
			( and
				( not ( not ( = x_1 y_2 ) ) )
				( not ( = lock_2 1 ) )
			)
		)
	)
)

( inv-constraint inv-f pre-f trans-f post-f )
( check-synth )
