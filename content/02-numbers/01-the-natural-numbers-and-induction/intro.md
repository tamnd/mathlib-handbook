# The natural numbers and induction

The type `ℕ` is the first number type of Mathlib, and induction is its first method of proof. This chapter starts from the axioms of Peano and builds the arithmetic of $\mathbb{N}$ with complete proofs.

The first section proves the recursion theorem, defines addition and multiplication, and proves their laws. It then derives induction from a start value, strong induction and induction in two steps from ordinary induction, and it shows the Mathlib names `Nat.le_induction`, `Nat.strong_induction_on` and `Nat.twoStepInduction`. The second section defines the order and the truncated subtraction of `ℕ`, proves the well ordering principle and infinite descent, and shows `Nat.find`, the least number with a property. The third section defines the factorial and the binomial coefficient by recursion, proves the factorial formula, and proves the binomial theorem `add_pow`.

The chapter needs Volume 1, Chapter 5 for the junk values. Chapter 2 uses the well ordering principle for the division algorithm and the factorial for the infinitude of primes, and Chapter 3 uses the binomial theorem for Fermat's little theorem.
