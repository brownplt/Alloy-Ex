module exercises/distribution

assert union {
	all s: set univ, p, q: univ->univ | s.(p + q) = s.p + s.q
	}
--check union for 4


assert difference {
	all s: set univ, p, q: univ->univ | s.(p - q) = s.p - s.q
	}
--check difference for 2


assert intersection {
	all s: set univ, p, q: univ->univ | s.(p & q) = s.p & s.q
	}
check intersection for 2
