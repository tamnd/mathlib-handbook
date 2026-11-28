---
title: Countable types and countable sets
kind: theory
modules:
  - Mathlib.Data.Set.Countable
  - Mathlib.Basic.Countable.Defs
  - Mathlib.Basic.Countable.Basic
  - Mathlib.Basic.Countable.Small
  - Mathlib.Data.Countable.Basic
  - Mathlib.Data.Countable.Defs
  - Mathlib.Data.Countable.Small
explains:
  E3: [Countable, Set.Countable, Set.countable_iUnion]
  E2: [Countable.exists_injective_nat, Function.Injective.countable, Function.Surjective.countable, Countable.of_equiv, Set.countable_coe_iff, Set.Countable.mono, Set.Countable.image, Set.Countable.union, Set.countable_iff_exists_surjective, Set.Countable.exists_eq_range, Set.Finite.countable, Set.countable_ofPred_finite_subset]
  E1: auto
families: []
requires: [V03.C05]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V03/C08/Examples.lean
  - MathlibHandbook/V03/C08/Exercises.lean
  - MathlibHandbook/V03/C08/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Countable types and countable sets

### Overview

A finite set has a size that is a natural number. The infinite sets have sizes too, and the smallest infinite size is the size of $\mathbb{N}$. A set is *countable* when its elements can be listed as $x_0, x_1, x_2, \ldots$, with repetitions allowed and with a finite list allowed. The natural numbers, the integers, the rationals, the pairs of natural numbers and the finite subsets of $\mathbb{N}$ are countable. The real numbers are not, by the theorem of Cantor in Section 2.

Countability is the property of a set that the arguments of analysis need most often. A countable union of null sets is a null set. A countable intersection of dense open sets of a complete metric space is dense. A measure is additive over countable families. Each of these results needs exactly the closure rules of this section: a subset, an image, a finite or countable union and a product of countable sets are countable.

This section defines a countable type and a countable set, proves the equivalence of the two usual definitions (an injection into $\mathbb{N}$, or a surjection from $\mathbb{N}$), computes the pairing function of $\mathbb{N} \times \mathbb{N}$ and proves the closure rules. The main theorem is that a countable union of countable sets is countable.

### Definitions

**Definition (Countable type).** A type $\alpha$ is *countable* if there is an injective map $f : \alpha \to \mathbb{N}$.

The map $f$ gives each element a code, and different elements get different codes. The definition does not ask that each number is a code. So a finite type is countable: the empty type has the empty map, and a type with $n$ elements has a bijection with $\{0, \ldots, n - 1\}$, which is an injection into $\mathbb{N}$. A countable type that is infinite is called *countably infinite* or *denumerable*. Section 2 shows that such a type is in bijection with $\mathbb{N}$.

::: mathlib
`Countable` · `Mathlib.Basic.Countable.Defs`

The class `Countable α` has one field, `exists_injective_nat' : ∃ f : α → ℕ, Injective f`. It is a class and a proposition. As a proposition it says nothing about which map $f$ is used, so it is the right hypothesis for a theorem. As a class it is found by instance search: `ℕ`, `ℤ`, `ℚ`, `Bool`, the finite types, and the products, sums, options and lists of countable types have instances. The class works for any `Sort`, so a proposition is a countable type too. The data form, with a chosen code, is the class `Encodable` of Section 2.

<?decl Countable?>
:::

**Definition (Countable set).** A subset $S$ of a type $\alpha$ is *countable* if the type of its elements is countable, that is, if there is an injective map $S \to \mathbb{N}$.

::: mathlib
`Set.Countable` · `Mathlib.Data.Set.Countable`

`s.Countable` is defined as `Countable s`, where `s` is coerced to the subtype `{x // x ∈ s}`. The bridge `Set.countable_coe_iff` turns one form into the other. The predicate form is convenient because of the dot notation: from `hs : s.Countable`, the terms `hs.mono h`, `hs.union ht` and `hs.image f` give the closure rules below. The tactic `exact Set.to_countable s` proves `s.Countable` from an instance `Countable α`.

<?decl Set.Countable?>
:::

**Definition (Pairing function).** The function $\pi : \mathbb{N} \times \mathbb{N} \to \mathbb{N}$ is $$\pi(a, b) = \begin{cases} b^2 + a & \text{if } a < b, \\ a^2 + a + b & \text{if } a \ge b. \end{cases}$$

The idea: the pairs $(a, b)$ with $\max(a, b) = s$ form the boundary of a square of side $s + 1$. There are $(s + 1)^2 - s^2 = 2s + 1$ of them. The function $\pi$ sends them, in order, to the $2s + 1$ numbers from $s^2$ to $s^2 + 2s$. The first $s$ pairs $(0, s), \ldots, (s - 1, s)$ go to $s^2, \ldots, s^2 + s - 1$. The next $s + 1$ pairs $(s, 0), \ldots, (s, s)$ go to $s^2 + s, \ldots, s^2 + 2s$.

::: mathlib
`Nat.pair` · `Mathlib.Data.Nat.Pairing`

`Nat.pair a b` is `if a < b then b * b + a else a * a + a + b`, the formula above. The inverse is `Nat.unpair n`, which computes $s = \lfloor \sqrt{n} \rfloor$ and reads the pair from $n - s^2$. The two laws are `Nat.unpair_pair` and `Nat.pair_unpair`, and the equivalence is `Nat.pairEquiv : ℕ × ℕ ≃ ℕ`. These declarations belong to the volume on numbers.

<?decl Nat.pair?>
:::

### Theorems and proofs

**Theorem (Injection and surjection).** Let $S$ be a nonempty set. Then $S$ is countable if and only if there is a surjective map $g : \mathbb{N} \to S$.

*Proof.* Assume first that $f : S \to \mathbb{N}$ is injective. Fix an element $s_0 \in S$. Define $g : \mathbb{N} \to S$ as follows. If $m$ is in the range of $f$, there is exactly one $x \in S$ with $f(x) = m$, because $f$ is injective, and $g(m) = x$. If $m$ is not in the range of $f$, then $g(m) = s_0$. For each $x \in S$, $g(f(x)) = x$. So $g$ is surjective.

Now assume that $g : \mathbb{N} \to S$ is surjective. For $x \in S$, the set $\{m \in \mathbb{N} : g(m) = x\}$ is not empty, and so it has a least element by the well ordering of $\mathbb{N}$. Let $f(x)$ be this least element. Then $g(f(x)) = x$. If $f(x) = f(y)$, then $x = g(f(x)) = g(f(y)) = y$. So $f$ is injective. $\square$

The hypothesis that $S$ is nonempty is needed for one direction only. The empty set is countable, but there is no map at all from $\mathbb{N}$ to the empty set. The second half of the proof uses no choice: the least element is a definite choice. The first half needs to decide whether $m$ is in the range of $f$, which a program cannot do in general. Mathlib uses classical logic there.

::: mathlib
`Set.countable_iff_exists_surjective` · `Mathlib.Data.Set.Countable`

The theorem in the form `s.Nonempty → (s.Countable ↔ ∃ f : ℕ → s, Surjective f)`. The form with a range is `Set.Countable.exists_eq_range`: a nonempty countable set is `Set.range f` for some `f : ℕ → α`. For types, `Function.Surjective.countable` says that the image of a countable type under a surjection is countable.

<?decl Set.countable_iff_exists_surjective?>
:::

**Theorem (Subsets, injections and images).** Let $\alpha$ and $\beta$ be types.

1. If $\beta$ is countable and $f : \alpha \to \beta$ is injective, then $\alpha$ is countable.
2. If $T$ is countable and $S \subseteq T$, then $S$ is countable.
3. If $S \subseteq \alpha$ is countable and $f : \alpha \to \beta$ is any map, then $f(S)$ is countable.
4. A finite set is countable.

*Proof.* 1. Let $c : \beta \to \mathbb{N}$ be injective. Then $c \circ f : \alpha \to \mathbb{N}$ is a composition of injective maps, so it is injective.

2. The inclusion $S \to T$ is injective. Apply part 1.

3. If $S$ is empty, then $f(S)$ is empty, and it is countable. If not, take a surjection $g : \mathbb{N} \to S$ by the previous theorem. Then $f \circ g : \mathbb{N} \to f(S)$ is surjective, so $f(S)$ is countable by the previous theorem again.

4. A finite set $S$ with $n$ elements has a bijection with $\{0, \ldots, n - 1\}$, which is an injection into $\mathbb{N}$. $\square$

::: mathlib
`Set.Countable.image` · `Mathlib.Data.Set.Countable`

The statement `s.Countable → ∀ f, (f '' s).Countable`. The other parts are `Function.Injective.countable` (for types), `Set.Countable.mono` (with the order of the arguments `s ⊆ t → t.Countable → s.Countable`), `Set.Finite.countable` and `Set.countable_range` for the range of a map from a countable type. Equivalent types have the same countability by `Countable.of_equiv`.

<?decl Set.Countable.image?>
:::

**Theorem (Pairs).** The pairing function $\pi$ is a bijection $\mathbb{N} \times \mathbb{N} \to \mathbb{N}$. In particular $\mathbb{N} \times \mathbb{N}$ is countable.

*Proof.* For $s \in \mathbb{N}$, let $B_s = \{(a, b) : \max(a, b) = s\}$ and $J_s = \{n \in \mathbb{N} : s^2 \le n \le s^2 + 2s\}$. The sets $B_0, B_1, \ldots$ partition $\mathbb{N} \times \mathbb{N}$, because each pair has exactly one maximum. The sets $J_0, J_1, \ldots$ partition $\mathbb{N}$: the number $s^2 + 2s$ is $(s + 1)^2 - 1$, so $J_s$ is the set of the $n$ with $s^2 \le n < (s + 1)^2$, and each $n$ lies in exactly one such interval, namely for $s = \lfloor \sqrt{n} \rfloor$. So it is enough to show that $\pi$ maps each $B_s$ bijectively onto $J_s$.

A pair in $B_s$ has one of two forms. The first form is $(a, s)$ with $a < s$, and then $\pi(a, s) = s^2 + a$, a number from $s^2$ to $s^2 + s - 1$. The second form is $(s, b)$ with $b \le s$, and then $a = s \ge b$, so $\pi(s, b) = s^2 + s + b$, a number from $s^2 + s$ to $s^2 + 2s$. On the first form, $\pi$ is injective in $a$, and its values are exactly the first $s$ numbers of $J_s$. On the second form, $\pi$ is injective in $b$, and its values are exactly the last $s + 1$ numbers of $J_s$. The two ranges are disjoint and cover $J_s$. So $\pi$ is a bijection from $B_s$ onto $J_s$. $\square$

**Theorem (Countable unions).** Let $\iota$ be a countable type, and let $(S_i)_{i \in \iota}$ be a family of countable subsets of $\alpha$. Then $\bigcup_{i \in \iota} S_i$ is countable.

*Proof.* Let $U = \bigcup_i S_i$. If $U$ is empty, it is countable. So let $U$ be nonempty, and fix $u_0 \in U$. Let $\iota'$ be the set of the $i$ with $S_i \ne \emptyset$. It is a subset of a countable type, so it is countable. It is nonempty, because $u_0$ lies in some $S_i$. So there is a surjection $h : \mathbb{N} \to \iota'$. For each $i \in \iota'$, choose a surjection $g_i : \mathbb{N} \to S_i$. This step uses the axiom of countable choice: there are infinitely many sets and a choice in each one. Define $G : \mathbb{N} \times \mathbb{N} \to U$ by $G(n, k) = g_{h(n)}(k)$. Each $x \in U$ lies in some $S_i$ with $i \in \iota'$. Write $i = h(n)$ and $x = g_i(k)$. Then $x = G(n, k)$, so $G$ is surjective. By the theorem (Pairs), $\mathbb{N} \times \mathbb{N}$ has a surjection from $\mathbb{N}$, namely $\pi^{-1}$. So $G \circ \pi^{-1} : \mathbb{N} \to U$ is surjective, and $U$ is countable. $\square$

::: mathlib
`Set.countable_iUnion` · `Mathlib.Data.Set.Countable`

The statement `[Countable ι] → (∀ i, (t i).Countable) → (⋃ i, t i).Countable`. The index is a type with a `Countable` instance. The form with an index set is `Set.Countable.biUnion`, and the form for a set of sets is `Set.Countable.sUnion`. The proof in Mathlib is short: `Set.iUnion_eq_range_psigma` writes the union as the range of the map $(i, x) \mapsto x$ on the dependent pairs with $x \in t_i$, the type of these pairs is countable by an instance, and `Set.countable_range` concludes. The instance for the pairs uses the coding of $\mathbb{N} \times \mathbb{N}$.

<?decl Set.countable_iUnion?>
:::

::: mathlib
`Set.Countable.union` · `Mathlib.Data.Set.Countable`

The union of two countable sets. It is the case $\iota = \mathrm{Bool}$ of the theorem above, but it is proved directly. The rules `Set.Countable.insert` and `Set.countable_singleton` give the small cases.

<?decl Set.Countable.union?>
:::

**Theorem (The integers and the rationals).** The sets $\mathbb{Z}$ and $\mathbb{Q}$ are countable.

*Proof.* For $\mathbb{Z}$, define $c(n) = 2n$ for $n \ge 0$ and $c(n) = -2n - 1$ for $n < 0$. The values on the nonnegative integers are the even numbers, and the values on the negative integers are the odd numbers $1, 3, 5, \ldots$. Each part is injective, and the two ranges are disjoint. So $c$ is injective.

For $\mathbb{Q}$, write each rational number in lowest terms as $p/q$ with $p \in \mathbb{Z}$, $q \ge 1$ and $\gcd(|p|, q) = 1$. This form is unique. Define $d(p/q) = \pi(c(p), q)$. If $d(p/q) = d(p'/q')$, then $(c(p), q) = (c(p'), q')$ because $\pi$ is injective, so $p = p'$ because $c$ is injective, and $q = q'$. So $d$ is injective. $\square$

**Theorem (Finite subsets of $\mathbb{N}$).** The set of the finite subsets of $\mathbb{N}$ is countable.

*Proof.* Send a finite set $F \subseteq \mathbb{N}$ to $b(F) = \sum_{i \in F} 2^i$. This is the number whose binary digits are $1$ exactly at the places in $F$. Two different finite sets give two different binary expansions, and the binary expansion of a number is unique. So $b$ is injective. In fact $b$ is a bijection onto $\mathbb{N}$, because each number has a binary expansion. $\square$

::: mathlib
`Set.countable_ofPred_finite_subset` · `Mathlib.Data.Set.Countable`

The general form: for a countable set `s`, the set `{t | t.Finite ∧ t ⊆ s}` of its finite subsets is countable. The old name `Set.countable_setOf_finite_subset` is deprecated in this edition. For types, the lists of a countable type form a countable type, by `List.countable`.

<?decl Set.countable_ofPred_finite_subset?>
:::

### Examples

**Example (Instances).** Instance search proves that $\mathbb{N} \times \mathbb{Z} \times \mathbb{Q}$ is countable, from the instances for the three factors and the instance for a product.

<?lean MathlibHandbook/V03/C08/Examples.lean#instances?>

**Example (Pairs).** The values of $\pi$ on the square $\{0, 1, 2\}^2$ are, by the formula: $\pi(0, 0) = 0$; $\pi(0, 1) = 1$, $\pi(1, 0) = 2$, $\pi(1, 1) = 3$; $\pi(0, 2) = 4$, $\pi(1, 2) = 5$, $\pi(2, 0) = 6$, $\pi(2, 1) = 7$, $\pi(2, 2) = 8$. Each shell $B_s$ fills the interval $J_s$: $B_1$ fills $\{1, 2, 3\}$ and $B_2$ fills $\{4, \ldots, 8\}$. In the other direction, take $n = 23$. Then $s = \lfloor \sqrt{23} \rfloor = 4$ and $n - s^2 = 7 \ge s$, so the pair is of the second form: $a = 4$ and $b = 7 - 4 = 3$. Check: $\pi(4, 3) = 16 + 4 + 3 = 23$. Mathlib checks the inverse law for all pairs.

<?lean MathlibHandbook/V03/C08/Examples.lean#pair?>

**Example (An injective code).** The class `Countable` gives an injective map to $\mathbb{N}$, but no particular map.

<?lean MathlibHandbook/V03/C08/Examples.lean#injective?>

**Example (The code of the integers).** The map $c$ of the theorem sends $0, -1, 1, -2, 2, -3$ to $0, 1, 2, 3, 4, 5$. So it lists $\mathbb{Z}$ as $0, -1, 1, -2, 2, -3, 3, \ldots$, and it is a bijection $\mathbb{Z} \to \mathbb{N}$. The code of the rational $-2/3$ is $d(-2/3) = \pi(c(-2), 3) = \pi(3, 3) = 9 + 3 + 3 = 15$.

**Example (A union).** The union of two countable sets of real numbers is countable.

<?lean MathlibHandbook/V03/C08/Examples.lean#union?>

**Example (A countable union).** A union of a sequence of countable sets is countable. For example the set of the real algebraic numbers is the union over $n \ge 1$ and over the integer polynomials of degree $n$ of the sets of their roots. There are countably many such polynomials, by the theorem (Pairs) applied to the coefficient lists, and each has at most $n$ roots. So the algebraic numbers form a countable set.

<?lean MathlibHandbook/V03/C08/Examples.lean#iUnion?>

**Example (Codes of finite sets).** The finite set $\{0, 2, 3\}$ has the code $2^0 + 2^2 + 2^3 = 13$, written $1101$ in base two. The code $10 = 1010_2$ belongs to the set $\{1, 3\}$. The empty set has the code $0$.

**Counterexample (A union over an uncountable index).** Each singleton $\{x\}$ with $x \in \mathbb{R}$ is countable, but the union over all $x \in \mathbb{R}$ is $\mathbb{R}$, which is not countable (Section 2). So the theorem (Countable unions) needs the index type to be countable. The union is over the type $\mathbb{R}$, and $\mathbb{R}$ has no `Countable` instance.

### Common errors

1. A learner reads "countable" as "countably infinite". In Mathlib, and in this book, a finite set is countable. Use `Set.Countable` together with `Set.Infinite` for "countably infinite".
2. A learner tries to prove `s.Countable` by `infer_instance`. The goal is a predicate on a set and not a class. Use `Set.to_countable s` when the ambient type is countable, or the closure rules.
3. A learner forgets the hypothesis `s.Nonempty` in `Set.countable_iff_exists_surjective`. The empty set has no surjection from $\mathbb{N}$.
4. A learner proves that a union over `i : ι` is countable and forgets the instance `Countable ι`. Lean then reports a failed instance search, not a false statement.

### The library around it

The file `Mathlib.Basic.Countable.Defs` has the classes `Countable` and `Uncountable` and the transfer rules along maps: `Function.Injective.countable`, `Function.Surjective.countable`, `Countable.of_equiv` and `Countable.exists_injective_nat`. The file `Mathlib.Basic.Countable.Basic` adds the instances for the standard types, for example `instCountableInt`. The file `Mathlib.Data.Set.Countable` has the predicate `Set.Countable` and its closure rules, all named in the pattern `Set.Countable.op` or `Set.countable_op`: `mono`, `image`, `union`, `insert`, `prod`, `biUnion`, `sUnion`, `of_sdiff`, and `Set.countable_iUnion`, `Set.countable_range`, `Set.countable_singleton`, `Set.countable_univ`. The bridges to the type form are `Set.countable_coe_iff`, `Set.Countable.to_subtype` and `Set.to_countable`, and the bridge to the surjective form is `Set.countable_iff_exists_surjective`. The bridge to cardinals is `Cardinal.mk_le_aleph0_iff`, in the volume on set theory. The table at the end lists the declarations of this section.

Besides the instances, `Mathlib.Basic.Countable.Basic` gives the form of countability with embeddings: `countable_iff_nonempty_embedding` says that $\alpha$ is countable exactly when there is an embedding $\alpha \hookrightarrow \mathbb{N}$, and `uncountable_iff_isEmpty_embedding` is the negation. The lemmas `Function.Embedding.countable` and `Function.Embedding.uncountable` move the two properties along an embedding, in opposite directions. The rules for the constructions read in both directions: `Option.countable_iff` says that `Option α` is countable exactly when $\alpha$ is, and `countable_left_of_prod_of_nonempty` recovers the countability of $\alpha$ from that of $\alpha \times \beta$ when $\beta$ is nonempty. For uncountable types, `Sigma.uncountable` says that a sigma type with one uncountable fiber is uncountable. The file `Mathlib.Basic.Countable.Small` gives the instance `Countable.toSmall`: a countable type is small in every universe, because it embeds in $\mathbb{N}$. Its contrapositive is `Uncountable.of_not_small`. The files `Mathlib.Data.Countable.Basic`, `Mathlib.Data.Countable.Defs` and `Mathlib.Data.Countable.Small` are deprecated modules with no declarations. Each one only imports the file of the same name under `Mathlib.Basic.Countable`, and a new file imports that path.

### Exercises

1. (A) Give `Nat.pair 2 3` from the definition, and give `Nat.unpair 30`.
2. (A) Explain why `Countable` is a proposition but `Encodable` is not, and why a theorem should take `[Countable α]` as its hypothesis.
3. (A) Give the code $d(3/4)$ of the rational number $3/4$ by the map of the theorem (The integers and the rationals).
4. (B) Prove that the set of the finite lists of natural numbers is countable. Hint: the lists of length $n$ form a set in bijection with $\mathbb{N}^n$; use the theorem (Pairs) and induction on $n$, then a countable union.
5. (B) Prove that a set $S \subseteq \mathbb{R}$ of pairwise disjoint open intervals is countable. Hint: each interval contains a rational number.
6. (B) Prove that the set of the finite subsets of a countable set is countable, by the method of the theorem (Finite subsets of $\mathbb{N}$).
7. (C) Prove that a monotone function $f : \mathbb{R} \to \mathbb{R}$ has at most countably many points of discontinuity. Hint: at a jump $x$, choose a rational in the open interval between the left and the right limits; these intervals are disjoint.
8. (L) Prove that a subset of a countable set is countable. The solution is `countable_mono_example`.
9. (L) Prove that the image of a countable set is countable. The solution is `countable_image_example`.
10. (L) Prove that a set with one element is countable. The solution is `countable_singleton_example`.
11. (L) Prove that the range of a map from `ℕ` is countable. The solution is `countable_range_example`.

### Notes and history

Cantor proved in 1874 that the algebraic numbers are countable and that the real numbers are not. The pairing function of `Nat.pair` is the one of Szudzik, which fills squares. The function of Cantor, $\binom{a + b + 1}{2} + b$, fills diagonals. The theorem that a countable union of countable sets is countable needs a choice of an enumeration for each set. Without the axiom of countable choice it can fail: in the model of Feferman and Lévy, $\mathbb{R}$ is a countable union of countable sets. Mathlib assumes choice, so the theorem holds there.

In Mathlib, the class `Countable` was added in 2022 by Yury Kudryashov to give a class that is a proposition, next to the older classes `Encodable` and `Denumerable` of Mario Carneiro. The file `Mathlib.Data.Set.Countable` comes from the Lean 3 file `data.set.countable` of Johannes Hölzl (2017).

### Reference

<?reference?>
