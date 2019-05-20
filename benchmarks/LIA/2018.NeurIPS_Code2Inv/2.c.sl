(set-logic LIA)

( declare-primed-var x Int )
( declare-primed-var y Int )

( declare-primed-var x_0 Int )
( declare-primed-var x_1 Int )
( declare-primed-var x_2 Int )
( declare-primed-var x_3 Int )
( declare-primed-var y_0 Int )
( declare-primed-var y_1 Int )
( declare-primed-var y_2 Int )
( declare-primed-var y_3 Int )

( synth-inv inv-f( ( x Int )( y Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( y_0 Int )( y_1 Int )( y_2 Int )( y_3 Int ) ) )

( define-fun pre-f ( ( x Int )( y Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( y_0 Int )( y_1 Int )( y_2 Int )( y_3 Int ) ) Bool
	( and
		( = x x_1 )
		( = y y_1 )
		( = x_1 1 )
		( = y_1 0 )
	)
)

( define-fun trans-f ( ( x Int )( y Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( y_0 Int )( y_1 Int )( y_2 Int )( y_3 Int )( x! Int )( y! Int )( x_0! Int )( x_1! Int )( x_2! Int )( x_3! Int )( y_0! Int )( y_1! Int )( y_2! Int )( y_3! Int ) ) Bool
	( or
		( and
			( = x_2 x )
			( = y_2 y )
			( = x_2 x! )
			( = y_2 y! )
			( = x x! )
		)
		( and
			( = x_2 x )
			( = y_2 y )
			( < y_2 1000 )
			( = x_3 ( + x_2 y_2 ) )
			( = y_3 ( + y_2 1 ) )
			( = x_3 x! )
			( = y_3 y! )
		)
	)
)

( define-fun post-f ( ( x Int )( y Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( y_0 Int )( y_1 Int )( y_2 Int )( y_3 Int ) ) Bool
	( or
		( not
			( and
				( = x x_2)
				( = y y_2)
			)
		)
		( not
			( and
				( not ( < y_2 1000 ) )
				( not ( >= x_2 y_2 ) )
			)
		)
	)
)

( inv-constraint inv-f pre-f trans-f post-f )
( check-synth )
