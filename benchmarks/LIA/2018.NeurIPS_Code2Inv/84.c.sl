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

( synth-inv inv-f( ( x Int )( y Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( y_0 Int )( y_1 Int )( y_2 Int ) ) )

( define-fun pre-f ( ( x Int )( y Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( y_0 Int )( y_1 Int )( y_2 Int ) ) Bool
	( and
		( = x x_1 )
		( = x_1 -50 )
	)
)

( define-fun trans-f ( ( x Int )( y Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( y_0 Int )( y_1 Int )( y_2 Int )( x! Int )( y! Int )( x_0! Int )( x_1! Int )( x_2! Int )( x_3! Int )( y_0! Int )( y_1! Int )( y_2! Int ) ) Bool
	( or
		( and
			( = x_2 x )
			( = y_1 y )
			( = x_2 x! )
			( = y_1 y! )
			( = y y! )
		)
		( and
			( = x_2 x )
			( = y_1 y )
			( < x_2 0 )
			( = x_3 ( + x_2 y_1 ) )
			( = y_2 ( + y_1 1 ) )
			( = x_3 x! )
			( = y_2 y! )
		)
	)
)

( define-fun post-f ( ( x Int )( y Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( y_0 Int )( y_1 Int )( y_2 Int ) ) Bool
	( or
		( not
			( and
				( = x x_2)
				( = y y_1)
			)
		)
		( not
			( and
				( not ( < x_2 0 ) )
				( not ( > y_1 0 ) )
			)
		)
	)
)

( inv-constraint inv-f pre-f trans-f post-f )
( check-synth )
