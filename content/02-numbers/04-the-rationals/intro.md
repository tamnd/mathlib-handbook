# The rationals

The type `ℚ` is the field of fractions of `ℤ`. This chapter builds the rational numbers as classes of fractions, shows how Lean stores a rational number in lowest terms, and gives the lemmas on the numerator and the denominator. It also introduces the type `ℚ≥0` of the rational numbers that are not negative.

The second section proves that `ℚ` is an archimedean ordered field in which each interval contains a rational number. Then it shows the limits of `ℚ`: $\sqrt 2$ is not rational, $\sqrt n$ is rational only for a perfect square $n$, and the rational root theorem restricts the rational roots of a polynomial with integer coefficients. The set $\{x \in \mathbb{Q} : x^2 < 2\}$ is bounded above, but it has no least upper bound in `ℚ`.

The chapter uses the integers and the division algorithm of Chapter 3 and the gcd of Chapter 2. Chapter 5 explains the casts from `ℕ` and `ℤ` into `ℚ`. Chapter 7 fills the gaps of `ℚ` and builds the real numbers as a complete ordered field.
