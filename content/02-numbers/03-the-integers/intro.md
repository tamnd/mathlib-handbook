# The integers

The type `ℤ` adds the negative numbers to `ℕ`, so that subtraction is always possible. This chapter shows how Lean builds `ℤ`, the induction on `ℤ`, the absolute value and the units $\pm 1$, and the division algorithm with the Euclidean convention of Mathlib for `/` and `%`.

The second section is about congruences modulo an integer. It proves that a congruence is compatible with addition, multiplication and powers, gives the rules of cancellation, solves linear congruences, proves the Chinese remainder theorem and Fermat's little theorem, and states the theorem of Euler.

The chapter uses the divisibility, the gcd and Bezout's identity of Chapter 2. Chapter 5 explains the casts between `ℕ` and `ℤ` that the statements here use. Chapter 6 makes the classes modulo $n$ into the ring `ZMod n`, and Chapter 4 uses `ℤ` to build the rationals.
