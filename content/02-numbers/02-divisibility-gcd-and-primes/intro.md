# Divisibility, gcd and primes

Divisibility, the greatest common divisor and the primes are the base of elementary number theory. This chapter proves the classical theorems on them with complete proofs, and it shows the Mathlib names for each.

The first section proves the division algorithm on `ℕ`, with the junk values $a / 0 = 0$ and $a \bmod 0 = a$ of Lean. It then proves that Euclid's algorithm computes the gcd, proves Bézout's identity in two ways, and derives Gauss's lemma and the relation between the gcd and the lcm. The Mathlib names are `Nat.gcd_eq_gcd_ab`, `Nat.gcdA` and `Nat.gcdB`. The second section defines the primes as Mathlib does, as irreducible elements. It proves that the least factor `Nat.minFac` of a number is prime, Euclid's lemma, the infinitude of primes and the fundamental theorem of arithmetic, with the list `Nat.primeFactorsList`.

The chapter needs Chapter 1: strong induction, the well ordering principle and the factorial. Chapter 3 uses Bézout's identity and Euclid's lemma for congruences, Chapter 4 uses the gcd for fractions in lowest terms, and Chapter 6 uses Bézout to find the units of `ZMod n`.
