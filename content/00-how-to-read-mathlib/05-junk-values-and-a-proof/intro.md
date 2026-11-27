# Junk values and a proof read line by line

This chapter explains a convention of Mathlib that surprises each new reader, and then reads full proofs of Mathlib. Section 5.1 shows the junk values: each function in Lean is total, so $1/0$, $5 - 7$ in $\mathbb{N}$, $\log 0$ and the derivative of a function with no derivative all have values. It proves which laws stay true with these values and which need a hypothesis. Section 5.2 reads a tactic proof of the companion package, the descent proof that no square is twice a square, line by line with its goals, and connects it to the irrationality of $\sqrt 2$ in Mathlib. Section 5.3 reads two proofs from the source of Mathlib: Euclid's theorem on primes as a term, and the formula of Gauss as a chain of equations.

The chapter needs Chapters 2 to 4. It is the end of the volume: after it the reader can read a statement of Mathlib, find it, and read its proof.
