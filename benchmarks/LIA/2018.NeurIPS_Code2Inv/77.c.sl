(set-logic LIA)

( declare-primed-var i Int )
( declare-primed-var x Int )
( declare-primed-var y Int )
( declare-primed-var tmp Int )

( declare-primed-var i_0 Int )
( declare-primed-var i_1 Int )
( declare-primed-var i_2 Int )
( declare-primed-var i_3 Int )
( declare-primed-var i_4 Int )
( declare-primed-var x_0 Int )
( declare-primed-var y_0 Int )

( synth-inv inv-f( ( i Int )( x Int )( y Int )( tmp Int )( i_0 Int )( i_1 Int )( i_2 Int )( i_3 Int )( i_4 Int )( x_0 Int )( y_0 Int ) ) )

( define-fun pre-f ( ( i Int )( x Int )( y Int )( tmp Int )( i_0 Int )( i_1 Int )( i_2 Int )( i_3 Int )( i_4 Int )( x_0 Int )( y_0 Int ) ) Bool
	( and
		( = i i_1 )
		( = x x_0 )
		( = y y_0 )
		( = i_1 0 )
		( >= x_0 0 )
		( >= y_0 0 )
		( >= x_0 y_0 )
	)
)

( define-fun trans-f ( ( i Int )( x Int )( y Int )( tmp Int )( i_0 Int )( i_1 Int )( i_2 Int )( i_3 Int )( i_4 Int )( x_0 Int )( y_0 Int )( i! Int )( x! Int )( y! Int )( tmp! Int )( i_0! Int )( i_1! Int )( i_2! Int )( i_3! Int )( i_4! Int )( x_0! Int )( y_0! Int ) ) Bool
	( or
		( and
			( = i_2 i )
			( = i_2 i! )
			( = i i! )
			( = x x! )
			( = y y! )
			(= tmp tmp! )
		)
		( and
			( = i_2 i )
			( < i_2 y_0 )
			( = i_3 ( + i_2 1 ) )
			( = i_4 i_3 )
			( = i_4 i! )
			(= x x_0 )
			(= x! x_0 )
			(= y y_0 )
			(= y! y_0 )
			(= tmp tmp! )
		)
		( and
			( = i_2 i )
			( not ( < i_2 y_0 ) )
			( = i_4 i_2 )
			( = i_4 i! )
			(= x x_0 )
			(= x! x_0 )
			(= y y_0 )
			(= y! y_0 )
			(= tmp tmp! )
		)
	)
)

( define-fun post-f ( ( i Int )( x Int )( y Int )( tmp Int )( i_0 Int )( i_1 Int )( i_2 Int )( i_3 Int )( i_4 Int )( x_0 Int )( y_0 Int ) ) Bool
	( or
		( not
			( and
				( = i i_2)
				( = x x_0)
				( = y y_0)
			)
		)
		( not
			( and
				( < i_2 y_0 )
				( not ( < i_2 x_0 ) )
			)
		)
	)
)

( inv-constraint inv-f pre-f trans-f post-f )
( check-synth )
