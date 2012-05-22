module exercises/properties

run {
	some r: univ->univ {
		some r				--yep		--nonempty
		r.r in r				--yep		--transitive
		no iden & r		--yep		--irreflexive
		~r in r				--NOPE		--symmetric
		~r.r in iden		--NOPE		--functional
		r.~r in iden		--NOPE		--injective
		univ in r.univ	--NOPE		--total
		univ in univ.r	--NOPE		--onto

		some x, y: univ | x->y in r	--nonempty
		

		}
	} for 4

--pred nonempty {
	
	--}
