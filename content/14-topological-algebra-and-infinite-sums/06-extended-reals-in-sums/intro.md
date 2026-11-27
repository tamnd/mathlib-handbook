# The extended reals in sums

Measure theory, probability and much of analysis add numbers with values in $[0, \infty]$. A length, an area, a probability or a norm in a space of sequences is a nonnegative quantity that can be infinite, and a countable sum of such quantities must have a value even when it diverges. Mathlib uses the type `ℝ≥0∞` of extended nonnegative reals for this purpose, with the type `ℝ≥0` of nonnegative reals as its finite part. The type `EReal` of extended reals $[-\infty, +\infty]$ and the type `ℕ∞` of extended natural numbers complete the picture.

Section 1 describes the topologies of these types. All of them carry the order topology. Addition is continuous on `ℝ≥0∞`, while multiplication fails to be continuous at the two pairs $(0, \infty)$ and $(\infty, 0)$, because Mathlib sets $0 \cdot \infty = 0$. The maps to $\mathbb{R}$ are continuous away from $\infty$ and not at $\infty$. Section 2 studies sums in `ℝ≥0∞`. Every family is summable, its sum is the supremum of its finite sums, two summations can always be exchanged, and the sum is finite exactly when the family is summable in `ℝ≥0`.

The chapter needs Volume 4 for the number systems, Volume 13 for the order topology, Chapter 4 for sums and Section 5.1 for sums of nonnegative terms. Volume 18 uses it for measures and integrals.
