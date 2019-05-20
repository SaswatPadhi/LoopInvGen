(set-logic LIA)

( declare-primed-var x Int )
( declare-primed-var y Int )
( declare-primed-var tmp Int )

( declare-primed-var x_0 Int )
( declare-primed-var x_1 Int )
( declare-primed-var x_2 Int )
( declare-primed-var y_0 Int )
( declare-primed-var y_1 Int )
( declare-primed-var y_2 Int )

( synth-inv inv-f( ( x Int )( y Int )( tmp Int )( x_0 Int )( x_1 Int )( x_2 Int )( y_0 Int )( y_1 Int )( y_2 Int ) ) )

( define-fun pre-f ( ( x Int )( y Int )( tmp Int )( x_0 Int )( x_1 Int )( x_2 Int )( y_0 Int )( y_1 Int )( y_2 Int ) ) Bool
	( and
		( = x x_0 )
		( = y y_0 )
		( >= x_0 0 )
		( <= x_0 2 )
		( <= y_0 2 )
		( >= y_0 0 )
	)
)

( define-fun trans-f ( ( x Int )( y Int )( tmp Int )( x_0 Int )( x_1 Int )( x_2 Int )( y_0 Int )( y_1 Int )( y_2 Int )( x! Int )( y! Int )( tmp! Int )( x_0! Int )( x_1! Int )( x_2! Int )( y_0! Int )( y_1! Int )( y_2! Int ) ) Bool
	( or
		( and
			( = x_1 x )
			( = y_1 y )
			( = x_1 x! )
			( = y_1 y! )
			( = x x! )
			( = y y! )
			(= tmp tmp! )
		)
		( and
			( = x_1 x )
			( = y_1 y )
			( = x_2 ( + x_1 2 ) )
			( = y_2 ( + y_1 2 ) )
			( = x_2 x! )
			( = y_2 y! )
			(= tmp tmp! )
		)
	)
)

( define-fun post-f ( ( x Int )( y Int )( tmp Int )( x_0 Int )( x_1 Int )( x_2 Int )( y_0 Int )( y_1 Int )( y_2 Int ) ) Bool
	( or
		( not
			( and
				( = x x_1)
				( = y y_1)
			)
		)
		( not
			( and
				( = x_1 4 )
				( not ( not ( = y_1 0 ) ) )
			)
		)
	)
)

( inv-constraint inv-f pre-f trans-f post-f )
( check-synth )
