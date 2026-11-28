# Krull dimension

The Krull dimension of a ring is the length of the longest chain of prime ideals. It is the algebraic form of the dimension of a variety: the coordinate ring of affine $n$-space has dimension $n$, a curve has dimension $1$, a point has dimension $0$. Dedekind domains are the rings of dimension at most $1$ among the Noetherian normal domains, and fields and Artinian rings are the rings of dimension $0$.

Section 1 defines the dimension as Mathlib does, through the order on the prime spectrum, and proves its basic properties: quotients do not raise it, integral extensions preserve it, PIDs that are not fields have dimension $1$, and polynomial rings over Noetherian rings add one. Section 2 turns to Noetherian local rings, where the dimension is bounded by the number of generators of the maximal ideal. The rings with equality are the regular local rings, the local rings of smooth points; in dimension $1$ they are exactly the DVRs of Chapter 3. Section 3 describes the length of a module, its support, the dimension of a module and the order of vanishing on a ring of dimension one. Section 4 describes regular elements and regular sequences, their behavior under permutation and flat maps, and the projective dimension of a quotient by a regular sequence.

The chapter uses the integral extensions of Chapter 1, Nakayama's lemma of Chapter 2, the DVRs of Chapter 3 and the Krull intersection theorem of Chapter 6. The heights of primes and Krull's principal ideal and height theorems are in Volume 9.

In Mathlib the dimension is `ringKrullDim R`, with values in `WithBot ℕ∞`, and regularity is the class `IsRegularLocalRing R`.
