# Fin n and ZMod n

The type `Fin n` has the $n$ numbers $0, 1, \dots, n - 1$, and the ring `ZMod n` is the ring $\mathbb{Z}/n\mathbb{Z}$ of the integers modulo $n$. This chapter turns the congruences of Chapter 3 into a ring and then studies the units of the ring.

The first section builds $\mathbb{Z}/n\mathbb{Z}$ with complete proofs, and shows how Mathlib defines `ZMod n` by cases, as `ℤ` for $n = 0$ and as `Fin n` for $n > 0$.

The second section finds the units: the class of $a$ is a unit if and only if $\gcd(a, n) = 1$, by Bézout's identity. So $\mathbb{Z}/p\mathbb{Z}$ is a field for a prime $p$, and only for a prime. The group of units gives Euler's theorem $a^{\varphi(n)} \equiv 1 \pmod n$, Fermat's little theorem in the form $a^p = a$ in `ZMod p`, and Wilson's theorem $(p - 1)! \equiv -1 \pmod p$.

The third section describes the maps between `Fin n` and `Fin (n + 1)`: the successor, the casts, the map `Fin.succAbove` that skips one value, the reversal, and the embeddings and the pigeonhole principle that come from them.

The fourth section describes tuples `Fin n → α`: the operations that add or remove an entry, the notation `![a, b, c]`, the tuples of natural numbers with a given sum, and the permutation that sorts a tuple.

The fifth section connects `ZMod n` to the quotients of `ℤ`, gives the Chinese remainder theorem as a ring isomorphism for many moduli, lifts units along the reduction maps, and defines the balanced residue `ZMod.valMinAbs`.

The chapter needs Chapter 2 (gcd and Bézout), Chapter 3 (congruences) and Chapter 5 (casts).
