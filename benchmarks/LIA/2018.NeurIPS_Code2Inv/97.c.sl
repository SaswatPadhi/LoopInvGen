(set-logic LIA)

( declare-primed-var i Int )
( declare-primed-var j Int )
( declare-primed-var x Int )
( declare-primed-var y Int )

( declare-primed-var i_0 Int )
( declare-primed-var i_1 Int )
( declare-primed-var i_2 Int )
( declare-primed-var i_3 Int )
( declare-primed-var j_0 Int )
( declare-primed-var j_1 Int )
( declare-primed-var j_2 Int )
( declare-primed-var j_3 Int )
( declare-primed-var x_0 Int )
( declare-primed-var y_0 Int )
( declare-primed-var y_1 Int )

( synth-inv inv-f( ( i Int )( j Int )( x Int )( y Int )( i_0 Int )( i_1 Int )( i_2 Int )( i_3 Int )( j_0 Int )( j_1 Int )( j_2 Int )( j_3 Int )( x_0 Int )( y_0 Int )( y_1 Int ) ) )

( define-fun pre-f ( ( i Int )( j Int )( x Int )( y Int )( i_0 Int )( i_1 Int )( i_2 Int )( i_3 Int )( j_0 Int )( j_1 Int )( j_2 Int )( j_3 Int )( x_0 Int )( y_0 Int )( y_1 Int ) ) Bool
	( and
		( = i i_1 )
		( = j j_1 )
		( = y y_1 )
		( = j_1 0 )
		( = i_1 0 )
		( = y_1 2 )
	)
)

( define-fun trans-f ( ( i Int )( j Int )( x Int )( y Int )( i_0 Int )( i_1 Int )( i_2 Int )( i_3 Int )( j_0 Int )( j_1 Int )( j_2 Int )( j_3 Int )( x_0 Int )( y_0 Int )( y_1 Int )( i! Int )( j! Int )( x! Int )( y! Int )( i_0! Int )( i_1! Int )( i_2! Int )( i_3! Int )( j_0! Int )( j_1! Int )( j_2! Int )( j_3! Int )( x_0! Int )( y_0! Int )( y_1! Int ) ) Bool
	( or
		( and
			( = i_2 i )
			( = j_2 j )
			( = i_2 i! )
			( = j_2 j! )
			( = x x_0 )
			( = x! x_0 )
			( = j j! )
			( = y y! )
		)
		( and
			( = i_2 i )
			( = j_2 j )
			( <= i_2 x_0 )
			( = i_3 ( + i_2 1 ) )
			( = j_3 ( + j_2 y_1 ) )
			( = i_3 i! )
			( = j_3 j! )
			(= x x_0 )
			(= x! x_0 )
			(= y y_1 )
			(= y! y_1 )
		)
	)
)

( define-fun post-f ( ( i Int )( j Int )( x Int )( y Int )( i_0 Int )( i_1 Int )( i_2 Int )( i_3 Int )( j_0 Int )( j_1 Int )( j_2 Int )( j_3 Int )( x_0 Int )( y_0 Int )( y_1 Int ) ) Bool
	( or
		( not
			( and
				( = i i_2)
				( = j j_2)
				( = x x_0 )
				( = y y_1)
			)
		)
		( not
			( and
				( not ( <= i_2 x_0 ) )
				( = y_1 1 )
				( not ( = i_2 j_2 ) )
			)
		)
	)
)

( inv-constraint inv-f pre-f trans-f post-f )
( check-synth )
