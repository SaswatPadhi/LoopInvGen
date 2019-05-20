(set-logic LIA)

( declare-primed-var i Int )
( declare-primed-var n Int )
( declare-primed-var sn Int )

( declare-primed-var i_0 Int )
( declare-primed-var i_1 Int )
( declare-primed-var i_2 Int )
( declare-primed-var i_3 Int )
( declare-primed-var n_0 Int )
( declare-primed-var sn_0 Int )
( declare-primed-var sn_1 Int )
( declare-primed-var sn_2 Int )
( declare-primed-var sn_3 Int )

( synth-inv inv-f( ( i Int )( n Int )( sn Int )( i_0 Int )( i_1 Int )( i_2 Int )( i_3 Int )( n_0 Int )( sn_0 Int )( sn_1 Int )( sn_2 Int )( sn_3 Int ) ) )

( define-fun pre-f ( ( i Int )( n Int )( sn Int )( i_0 Int )( i_1 Int )( i_2 Int )( i_3 Int )( n_0 Int )( sn_0 Int )( sn_1 Int )( sn_2 Int )( sn_3 Int ) ) Bool
	( and
		( = i i_1 )
		( = sn sn_1 )
		( = sn_1 0 )
		( = i_1 1 )
	)
)

( define-fun trans-f ( ( i Int )( n Int )( sn Int )( i_0 Int )( i_1 Int )( i_2 Int )( i_3 Int )( n_0 Int )( sn_0 Int )( sn_1 Int )( sn_2 Int )( sn_3 Int )( i! Int )( n! Int )( sn! Int )( i_0! Int )( i_1! Int )( i_2! Int )( i_3! Int )( n_0! Int )( sn_0! Int )( sn_1! Int )( sn_2! Int )( sn_3! Int ) ) Bool
	( or
		( and
			( = i_2 i )
			( = sn_2 sn )
			( = i_2 i! )
			( = sn_2 sn! )
			( = n n_0 )
			( = n! n_0 )
			( = sn sn! )
		)
		( and
			( = i_2 i )
			( = sn_2 sn )
			( <= i_2 n_0 )
			( = i_3 ( + i_2 1 ) )
			( = sn_3 ( + sn_2 1 ) )
			( = i_3 i! )
			( = sn_3 sn! )
			(= n n_0 )
			(= n! n_0 )
		)
	)
)

( define-fun post-f ( ( i Int )( n Int )( sn Int )( i_0 Int )( i_1 Int )( i_2 Int )( i_3 Int )( n_0 Int )( sn_0 Int )( sn_1 Int )( sn_2 Int )( sn_3 Int ) ) Bool
	( or
		( not
			( and
				( = i i_2)
				( = n n_0 )
				( = sn sn_2)
			)
		)
		( not
			( and
				( not ( <= i_2 n_0 ) )
				( not ( = sn_2 n_0 ) )
				( not ( = sn_2 0 ) )
			)
		)
	)
)

( inv-constraint inv-f pre-f trans-f post-f )
( check-synth )
