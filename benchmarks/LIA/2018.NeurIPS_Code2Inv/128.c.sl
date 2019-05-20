(set-logic LIA)

( declare-primed-var x Int )
( declare-primed-var y Int )

( declare-primed-var x_0 Int )
( declare-primed-var x_1 Int )
( declare-primed-var x_2 Int )
( declare-primed-var x_3 Int )
( declare-primed-var y_0 Int )

( synth-inv inv-f( ( x Int )( y Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( y_0 Int ) ) )

( define-fun pre-f ( ( x Int )( y Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( y_0 Int ) ) Bool
	( and
		( = x x_1 )
		( = x_1 1 )
	)
)

( define-fun trans-f ( ( x Int )( y Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( y_0 Int )( x! Int )( y! Int )( x_0! Int )( x_1! Int )( x_2! Int )( x_3! Int )( y_0! Int ) ) Bool
	( or
		( and
			( = x_2 x )
			( = x_2 x! )
			( = y y_0 )
			( = y! y_0 )
		)
		( and
			( = x_2 x )
			( < x_2 y_0 )
			( = x_3 ( + x_2 x_2 ) )
			( = x_3 x! )
			(= y y_0 )
			(= y! y_0 )
		)
	)
)

( define-fun post-f ( ( x Int )( y Int )( x_0 Int )( x_1 Int )( x_2 Int )( x_3 Int )( y_0 Int ) ) Bool
	( or
		( not
			( and
				( = x x_2)
				( = y y_0 )
			)
		)
		( not
			( and
				( not ( < x_2 y_0 ) )
				( not ( >= x_2 1 ) )
			)
		)
	)
)

( inv-constraint inv-f pre-f trans-f post-f )
( check-synth )
