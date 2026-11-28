---
title: Pairing, distance and other constructions on ℕ
kind: api
modules:
  - Mathlib.Data.Nat.Notation
  - Mathlib.Data.Nat.Pairing
  - Mathlib.Data.Nat.Dist
  - Mathlib.Data.Nat.PSub
  - Mathlib.Data.Nat.Upto
  - Mathlib.Data.Nat.EvenOddRec
  - Mathlib.Data.Nat.WithBot
  - Mathlib.Data.Nat.Set
  - Mathlib.Data.Nat.Order.Lemmas
  - Mathlib.Data.Nat.Lattice
  - Mathlib.Data.Nat.SuccPred
explains:
  E2: [Nat.pair, Nat.unpair, Nat.unpair_pair, Nat.pairEquiv, Nat.dist, Nat.psub, Nat.Upto.wf, Nat.evenOddRec, Nat.set_eq_univ]
  E1: auto
families: []
requires: [V01.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Pairing, distance and other constructions on ℕ

### Overview

This section collects small constructions on the natural numbers. Each one is short, and each one appears again in other parts of the library. The pairing function `Nat.pair` is a bijection from $\mathbb{N} \times \mathbb{N}$ onto $\mathbb{N}$, with the inverse `Nat.unpair`. Computability theory and the theory of countable types use it to code pairs as numbers. The distance `Nat.dist` is $|n - m|$ without a cast to the integers. The partial subtraction `Nat.psub` returns no value when the true difference is negative. The type `Nat.Upto p` gives a well-founded order for a search with no known upper bound. The recursor `Nat.evenOddRec` proves a statement for $2n$ and for $2n + 1$ from the statement for $n$. The type `WithBot ℕ` adds a bottom element $\bot$ to $\mathbb{N}$, and the library uses it for the degree of a polynomial.

The module `Mathlib.Data.Nat.Notation` declares the notation ℕ for the type of natural numbers. Its one declaration is the parser `termℕ`. Each module of the library that writes ℕ imports it.

### The library around it

#### The pairing function

The function `Nat.pair a b` is $b^2 + a$ if $a < b$ and $a^2 + a + b$ otherwise. The table shows its first values, with $a$ for the row and $b$ for the column.

| | $b = 0$ | $b = 1$ | $b = 2$ | $b = 3$ |
|---|---|---|---|---|
| $a = 0$ | 0 | 1 | 4 | 9 |
| $a = 1$ | 2 | 3 | 5 | 10 |
| $a = 2$ | 6 | 7 | 8 | 11 |
| $a = 3$ | 12 | 13 | 14 | 15 |

The numbers from $s^2$ to $(s + 1)^2 - 1$ fill the pairs with $\max(a, b) = s$. They go down column $s$ first, and then along row $s$ from the left. The inverse `Nat.unpair n` reads this rule backward. It takes $s = \lfloor \sqrt{n} \rfloor$ (the integer square root) and the remainder $r = n - s^2$. If $r < s$, the pair is $(r, s)$. Otherwise the pair is $(s, r - s)$.

**Theorem (`Nat.unpair_pair` and `Nat.pair_unpair`).** For all $a, b$, $\mathrm{unpair}(\mathrm{pair}(a, b)) = (a, b)$. For all $n$, $\mathrm{pair}(\mathrm{unpair}(n)) = n$.

*Proof.* Let $a < b$. Then $b^2 \leq b^2 + a < (b + 1)^2$, so $\lfloor \sqrt{b^2 + a} \rfloor = b$, the remainder is $a$ and $a < b$. So the result is $(a, b)$. Let $a \geq b$. Then $a^2 \leq a^2 + a + b \leq a^2 + 2a < (a + 1)^2$, so the square root is $a$ and the remainder is $a + b \geq a$. So the result is $(a, a + b - a) = (a, b)$. For the second claim, let $s$ and $r$ be as above, so $0 \leq r \leq 2s$. If $r < s$, then $\mathrm{pair}(r, s) = s^2 + r = n$. If $r \geq s$, then $r - s \leq s$, and $\mathrm{pair}(s, r - s) = s^2 + s + (r - s) = n$. $\square$

The two inverse functions give the equivalence `Nat.pairEquiv : ℕ × ℕ ≃ ℕ`. So `Nat.pair_eq_pair` says that `Nat.pair` is injective, and `Nat.surjective_unpair` says that `Nat.unpair` is surjective. The other lemmas give bounds and monotonicity.

| Lean name | Statement |
|---|---|
| `Nat.left_le_pair`, `Nat.right_le_pair` | $a \leq \mathrm{pair}(a, b)$ and $b \leq \mathrm{pair}(a, b)$ |
| `Nat.add_le_pair` | $m + n \leq \mathrm{pair}(m, n)$ |
| `Nat.unpair_left_le`, `Nat.unpair_right_le` | each coordinate of $\mathrm{unpair}(n)$ is at most $n$ |
| `Nat.unpair_lt` | for $n \geq 1$, the first coordinate is less than $n$ |
| `Nat.pair_lt_pair_left`, `Nat.pair_lt_pair_right` | `Nat.pair` is strictly increasing in each argument |
| `Nat.max_sq_add_min_le_pair` | $\max(m, n)^2 + \min(m, n) \leq \mathrm{pair}(m, n)$ |
| `Nat.pair_lt_max_add_one_sq` | $\mathrm{pair}(m, n) < (\max(m, n) + 1)^2$ |

The lemma `Nat.unpair_lt` allows recursion through `Nat.unpair`: a function can call itself on the coordinates of $n$, and the argument decreases. The coding of primitive recursive functions in computability theory uses this. The last lemmas of the module change a double index into a single one: `Set.iUnion_unpair` says that $\bigcup_n f(\mathrm{unpair}(n)) = \bigcup_i \bigcup_j f(i, j)$, and `iSup_unpair` and `iInf_unpair` are the same for a complete lattice.

#### Distance

The function `Nat.dist n m` is $(n - m) + (m - n)$ with truncated subtraction. One of the two terms is $0$, so the value is $|n - m|$ (`Nat.dist_eq_max_sub_min`). The lemmas are the axioms of a metric and the behaviour under translation and scaling.

| Lean name | Statement |
|---|---|
| `Nat.dist_self`, `Nat.dist_eq_zero` | $\mathrm{dist}(n, n) = 0$ |
| `Nat.dist_pos_of_ne` | $i \neq j$ gives $0 < \mathrm{dist}(i, j)$ |
| `Nat.dist_comm` | $\mathrm{dist}(n, m) = \mathrm{dist}(m, n)$ |
| `Nat.dist.triangle_inequality` | $\mathrm{dist}(n, k) \leq \mathrm{dist}(n, m) + \mathrm{dist}(m, k)$ |
| `Nat.dist_eq_sub_of_le` | $n \leq m$ gives $\mathrm{dist}(n, m) = m - n$ |
| `Nat.dist_add_add_left` | $\mathrm{dist}(k + n, k + m) = \mathrm{dist}(n, m)$ |
| `Nat.dist_mul_left` | $\mathrm{dist}(k n, k m) = k \cdot \mathrm{dist}(n, m)$ |
| `Nat.dist_succ_succ` | $\mathrm{dist}(i + 1, j + 1) = \mathrm{dist}(i, j)$ |

The lemma `Nat.dist_eq_intro` says that $n + m = k + l$ gives $\mathrm{dist}(n, k) = \mathrm{dist}(l, m)$. The metric space structure on ℕ in topology does not use `Nat.dist`. It comes from the inclusion into $\mathbb{R}$. So `Nat.dist` is for proofs that stay inside ℕ.

#### Partial subtraction

Truncated subtraction gives $m - n = 0$ for $m < n$. The function `Nat.psub m n` gives a value of type `Option ℕ` instead: `some (m - n)` if $n \leq m$ and the empty value if $m < n$. It is defined from the partial predecessor `Nat.ppred`, which sends $0$ to the empty value and $n + 1$ to `some n`, by recursion on $n$ in the option monad. The lemmas `Nat.psub_eq_sub` and `Nat.psub_eq_none` give the two cases, `Nat.psub_eq_some` says that `Nat.psub m n = some k` exactly when $k + n = m$, and `Nat.sub_eq_psub` recovers the truncated subtraction with the default value $0$. The function `Nat.psub'` is the direct definition by the two cases, and `Nat.psub'_eq_psub` says that the two definitions agree.

#### Searches without a bound

The type `Nat.Upto p` is the subtype of the $i$ such that no $j < i$ satisfies $p$. It is an initial segment of ℕ, up to and including the first element of $p$. The relation `Nat.Upto.GT p` is $>$ on this type.

**Theorem (`Nat.Upto.wf`).** If some $x$ satisfies $p$, then `Nat.Upto.GT p` is well-founded.

*Proof.* Each element $y$ of `Nat.Upto p` satisfies $y \leq x$, because $x$ satisfies $p$ and so $x$ is not below $y$. So $y > z$ gives $x - y < x - z$. The relation is the inverse image of $<$ under $y \mapsto x - y$, and the inverse image of a well-founded relation is well-founded. $\square$

So a search that starts at `Nat.Upto.zero` and steps with `Nat.Upto.succ` while $p$ fails ends. The search does not need a bound, and $p$ does not need to be decidable in the proof of termination. The function `Nat.find` uses a similar relation for decidable predicates.

#### Recursion on the binary digits

The recursor `Nat.evenOddRec` builds a value of $P(n)$ for each $n$ from three inputs: a value of $P(0)$, a step from $P(i)$ to $P(2i)$, and a step from $P(i)$ to $P(2i + 1)$. It is the binary recursion `Nat.binaryRec`, with the last binary digit written as an even or an odd case. The computation rules are `Nat.evenOddRec_zero`, `Nat.evenOddRec_even` and `Nat.evenOddRec_odd`. The last two need the condition that the even step at $0$ gives the start value back, because $0 = 2 \cdot 0$. The strong form `Nat.evenOddStrongRec` gives the step for $2n$ or $2n + 1$ access to all smaller numbers.

A proof by `Nat.evenOddRec` uses about $\log_2 n$ steps to reach $n$. The proofs of the doubling formulas of the Fibonacci numbers and of the identities of binary length follow this pattern.

#### The type `WithBot ℕ`

The type `WithBot ℕ` is ℕ with a new least element $\bot$. The degree of a polynomial has this type, with $\deg 0 = \bot$ (`Polynomial.degree`). The module `Mathlib.Data.Nat.WithBot` gives the arithmetic facts that degree computations need. The sum $n + m$ is $\bot$ when one of the summands is $\bot$, so a sum with a natural value has two natural summands. The lemmas `Nat.WithBot.add_eq_zero_iff`, `Nat.WithBot.add_eq_one_iff`, `Nat.WithBot.add_eq_two_iff` and `Nat.WithBot.add_eq_three_iff` list the decompositions of $0$, $1$, $2$ and $3$. The lemma `Nat.WithBot.lt_zero_iff` says that $\bot$ is the only element below $0$, and `Nat.WithBot.add_one_le_of_lt` is the discrete order: $n < m$ gives $n + 1 \leq m$. The instance `Nat.WithBot.instWellFoundedRelationWithBot` allows well-founded recursion on a degree.

#### Sets of natural numbers

The module `Mathlib.Data.Nat.Order.Lemmas` contains the set form of induction.

**Theorem (`Nat.set_eq_univ`).** A set $S \subseteq \mathbb{N}$ is all of ℕ if and only if $0 \in S$ and $k \in S$ gives $k + 1 \in S$ for each $k$.

*Proof.* One direction is clear. For the other, apply induction to the predicate $n \in S$. $\square$

The lemma `Nat.exists_not_and_succ_of_not_zero_of_exists` is the contrapositive form: if $p(0)$ fails and $p(n)$ holds for some $n$, there is an $n$ with $\neg p(n)$ and $p(n + 1)$. The same module puts an order on subtypes. `Nat.Subtype.orderBot` makes the least element of a nonempty decidable set the bottom element of the subtype, and `Nat.Subtype.coe_bot` says that this element is the value of `Nat.find`.

The module `Mathlib.Data.Nat.Set` describes ranges. The range of the successor is the set of positive numbers (`Nat.range_succ`), and the range of $f$ is $f(0)$ together with the range of $f \circ \mathrm{succ}$ (`Nat.range_of_succ`).

#### Common errors

1. `Nat.pair` is not the Cantor pairing $\frac{(a + b)(a + b + 1)}{2} + b$. It orders the pairs by $\max(a, b)$, so a statement about diagonals $a + b = s$ does not hold for it. Use `Nat.pairEquiv` when only a bijection is necessary, and do not use the values.
2. The coordinates of `Nat.unpair n` are `(Nat.unpair n).1` and `(Nat.unpair n).2`. A rewrite with `Nat.pair_unpair` needs the term in exactly this form. A term `Nat.pair a b` with `(a, b) = Nat.unpair n` from a hypothesis needs `Nat.pair_eq_of_unpair_eq`.
3. In `WithBot ℕ`, $\bot + n = \bot$ for each $n$. So $a + b = a + c$ does not give $b = c$ when $a = \bot$, and a cancellation needs the hypothesis $a \neq \bot$. The omega tactic does not work on this type. Move the statement to ℕ with the cast first.

### Exercises

1. (A) Compute `Nat.pair 3 5`, `Nat.pair 5 3` and `Nat.unpair 30`. Check each result with the rule of the table.
2. (A) Prove `Nat.dist_comm` and `Nat.dist_self` from the definition $(n - m) + (m - n)$.
3. (B) Prove `Nat.unpair_lt`: for $n \geq 1$, the first coordinate of `Nat.unpair n` is less than $n$.
4. (B) Use `Nat.evenOddRec` to define a function `ℕ → ℕ` that counts the ones in the binary digits of $n$, and prove that its value at $2^k - 1$ is $k$.
5. (B) Prove `Nat.psub_eq_none` by induction on $n$ from the definition with `Nat.ppred`.
6. (C) Prove that the Cantor function $(a, b) \mapsto \frac{(a + b)(a + b + 1)}{2} + b$ is a bijection from $\mathbb{N} \times \mathbb{N}$ onto $\mathbb{N}$, and find an $n$ where it differs from `Nat.pair` with the same order of arguments.

### Reference

<?reference?>
