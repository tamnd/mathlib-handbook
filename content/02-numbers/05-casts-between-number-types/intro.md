# Casts between number types

A natural number is also an integer, a rational number and a real number. In Lean these are four different types, and a function called a cast connects each type to the next. This chapter studies the casts as mathematics and as a tool of proof.

The first section proves that the cast from $\mathbb{N}$ is the unique additive map that sends $1$ to $1$, and that the cast from $\mathbb{Z}$ is the unique map of rings. It proves the rules for sums, products, powers and the order, and it shows where they fail: the truncated subtraction and the rounded division of $\mathbb{N}$. The second section gives the method of proof: move a statement to a bigger type, prove it there, and come back with the injectivity of the cast. It describes the tactics `push_cast`, `norm_cast`, `exact_mod_cast`, `zify`, `qify` and `lift`. The third section collects the rules for the cast from `ℚ` and `ℚ≥0`, which need characteristic zero for the algebra and a linear order for the inequalities, and the cast lemmas from `ℕ` for noncommutative semirings, ordered rings, functions, pairs and intervals.

The chapter needs Chapters 1 to 4. Chapters 6 to 8 and almost every later volume use the casts.
