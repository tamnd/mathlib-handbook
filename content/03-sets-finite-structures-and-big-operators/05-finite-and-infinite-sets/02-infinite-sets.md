---
title: Infinite types and infinite sets
kind: theory
modules:
  - Mathlib.Data.Fintype.EquivFin
  - Mathlib.Data.Set.Finite.Lattice
explains:
  E3: [Infinite, Infinite.exists_notMem_finset, Infinite.natEmbedding]
  E2: [Infinite.exists_subset_card_eq, Infinite.exists_superset_card_eq, Set.Infinite.exists_subset_card_eq, Set.Infinite.exists_notMem_finset, Infinite.of_injective, Infinite.of_surjective, Infinite.of_injective_to_set, Int.infinite, Set.infinite_of_injective_forall_mem, Set.infinite_of_not_bddAbove, Set.Finite.bddAbove, Set.infinite_univ, Set.Infinite.ncard, Set.encard_eq_top_iff, Set.infinite_coe_iff]
  E1: auto
families: []
requires: [V03.C03, V03.C04]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V03/C05/Examples.lean
  - MathlibHandbook/V03/C05/Exercises.lean
  - MathlibHandbook/V03/C05/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Infinite types and infinite sets

### Overview

A set is infinite when it is not finite. This definition by a negation is short, but it gives no direct way to use the hypothesis. The work of this section is to turn "not finite" into positive statements that a proof can use: an infinite type has an element outside each finset, it has finsets of each size, and it contains a copy of $\mathbb{N}$. In the other direction the section gives the standard ways to prove that a set is infinite: an injection from an infinite set, an unbounded set of natural numbers, and an injective self-map that is not surjective.

The main theorems are three. A set of natural numbers is infinite exactly when it has no upper bound. There are infinitely many primes, by the proof of Euclid. A type is infinite exactly when it has an injective map to itself that is not surjective, which is the definition of Dedekind. The section ends with the counts of an infinite set, which are $0$ for `ncard` and $\infty$ for `encard`.

### Definitions

**Definition (Infinite type and infinite set).** A type $\alpha$ is *infinite* if it is not finite, that is, if there is no bijection $\alpha \to \mathrm{Fin}\ n$ for any $n$. A set $s$ is infinite if the type of its elements is infinite.

::: mathlib
`Infinite` · `Mathlib.Basic.Finite.Defs`

`Infinite α` is a class with one field, `not_finite : ¬ Finite α`. It is a class, not only the negation, so that instance search can find it: `Infinite ℕ`, `Infinite ℤ`, `Infinite ℚ` and `Infinite ℝ` are instances, and the instance for a product or a function type follows from the instances of its parts. The lemma `not_finite_iff_infinite` translates between the two forms, and `Set.infinite_coe_iff` says that `Infinite s` for the subtype is `s.Infinite` for the set.

<?decl Infinite?>
:::

**Definition (Bounded above).** A set $s$ of natural numbers is *bounded above* if there is a $b$ with $x \le b$ for each $x \in s$.

**Definition (Dedekind infinite).** A type $\alpha$ is *Dedekind infinite* if there is an injective map $f : \alpha \to \alpha$ that is not surjective.

### Theorems and proofs

**Theorem (An element outside each finset).** A type $\alpha$ is infinite if and only if for each finset $t$ of $\alpha$ there is an $x \in \alpha$ with $x \notin t$.

*Proof.* Assume that $\alpha$ is infinite, and let $t$ be a finset. If each $x$ were in $t$, then $t$ would be a finite type structure on $\alpha$, and $\alpha$ would be finite by Section 1. So some $x$ is not in $t$. Conversely, assume that $\alpha$ is finite. Then it has a finite type structure $U$, a finset that contains each element. For $t = U$ no $x$ is outside $t$. $\square$

::: mathlib
`Infinite.exists_notMem_finset` · `Mathlib.Data.Fintype.EquivFin`

The statement is `∃ x, x ∉ s` for a finset `s`, under `[Infinite α]`. The form for sets, `Set.Infinite.exists_notMem_finset`, gives a point `a ∈ s` with `a ∉ t`. An older name of the same lemma is `Infinite.exists_not_mem_finset`, from before `not_mem` became `notMem` in the names of the library.

<?decl Infinite.exists_notMem_finset?>
:::

**Theorem (The natural numbers are infinite).** The type $\mathbb{N}$ is infinite.

*Proof.* Let $t$ be a finset of natural numbers, and let $m = \sum_{x \in t} x$. Each $x \in t$ satisfies $x \le m$, since the other terms of the sum are not negative. So $m + 1$ is larger than each element of $t$, and $m + 1 \notin t$. By the last theorem, $\mathbb{N}$ is infinite. $\square$

**Theorem (Injections and surjections).** Let $f : \beta \to \alpha$. If $\beta$ is infinite and $f$ is injective, then $\alpha$ is infinite. If $\beta$ is infinite and $g : \alpha \to \beta$ is surjective, then $\alpha$ is infinite.

*Proof.* These are the contrapositives of the rules of Section 1. If $\alpha$ were finite and $f$ injective, then $\beta$ would be finite. If $\alpha$ were finite and $g$ surjective, then $\beta$ would be finite. $\square$

The integers are infinite, because $n \mapsto n$ from $\mathbb{N}$ to $\mathbb{Z}$ is injective. The rationals and the reals are infinite for the same reason. A set $s \subseteq \alpha$ is infinite when there is an injective map $f$ from an infinite type with each value in $s$.

::: mathlib
`Infinite.of_injective` · `Mathlib.Data.Fintype.EquivFin`

The instance `[Infinite β]` is on the domain, and the map and the injectivity are explicit. `Infinite.of_surjective` is the second rule. The form for sets, `Set.infinite_of_injective_forall_mem`, takes an injective `f : α → β` with `∀ x, f x ∈ s` and gives `s.Infinite`. The instance `Int.infinite` is proved with the first rule.

<?decl Infinite.of_injective?>
:::

**Theorem (Finsets of each size).** Let $\alpha$ be infinite and let $n$ be a natural number. Then $\alpha$ has a finset with exactly $n$ elements. More generally, each finset $s$ with $|s| \le n$ is contained in a finset with exactly $n$ elements.

*Proof.* Use induction on $n - |s|$. If $|s| = n$, take $s$ itself. If $|s| < n$, the first theorem gives an $x \notin s$. The finset $s \cup \{x\}$ has $|s| + 1 \le n$ elements, and $n - |s \cup \{x\}| = n - |s| - 1$. By the induction hypothesis it is contained in a finset $t$ with $n$ elements, and then $s \subseteq t$. For the first claim, take $s = \emptyset$. $\square$

::: mathlib
`Infinite.exists_subset_card_eq` · `Mathlib.Data.Fintype.EquivFin`

The name is historical: the statement is `∃ s : Finset α, s.card = n`, with no superset. The general form is `Infinite.exists_superset_card_eq`. The form for an infinite set `s` is `Set.Infinite.exists_subset_card_eq`, which gives a finset `t` with `↑t ⊆ s` and `t.card = n`.

<?decl Infinite.exists_subset_card_eq?>
:::

**Theorem (A copy of the natural numbers).** If $\alpha$ is infinite, there is an injective map $a : \mathbb{N} \to \alpha$.

*Proof.* Define $a_0, a_1, a_2, \ldots$ by recursion. Assume that $a_0, \ldots, a_{n-1}$ are defined. The finset $\{a_0, \ldots, a_{n-1}\}$ is not all of $\alpha$, by the first theorem, so choose $a_n$ outside it. Then $a_n \ne a_i$ for $i < n$. For $i < j$ this gives $a_j \ne a_i$, so the map $n \mapsto a_n$ is injective. $\square$

The proof makes infinitely many choices, one at each step. This uses a form of the axiom of choice, the axiom of dependent choice. Without any choice there can be infinite sets with no injection from $\mathbb{N}$. Mathlib works with the axiom of choice, so the theorem holds there, but the map is a noncomputable definition.

::: mathlib
`Infinite.natEmbedding` · `Mathlib.Data.Fintype.EquivFin`

The result is a bundled embedding `ℕ ↪ α`, a function with a proof of injectivity. It is a noncomputable definition, built by the recursion above with `Classical.choose`. The form for an infinite set is `Set.Infinite.natEmbedding s hs : ℕ ↪ s`. The converse is `Infinite.of_injective` applied to the embedding.

<?decl Infinite.natEmbedding?>
:::

**Theorem (Dedekind).** A type $\alpha$ is infinite if and only if there is an injective map $f : \alpha \to \alpha$ that is not surjective.

*Proof.* Assume that $f : \alpha \to \alpha$ is injective and not surjective. If $\alpha$ were finite, the theorem on injective and surjective maps of Chapter 4 would make $f$ surjective. So $\alpha$ is infinite.

Conversely, let $\alpha$ be infinite, and let $a : \mathbb{N} \to \alpha$ be injective, by the last theorem. Define $f : \alpha \to \alpha$ by $f(a_n) = a_{n+1}$ for each $n$, and $f(x) = x$ for each $x$ that is not a value of $a$. This is well defined, because each value of $a$ is $a_n$ for exactly one $n$. The map $f$ is injective. There are three cases for $f(x) = f(y)$. If $x = a_n$ and $y = a_m$, then $a_{n+1} = a_{m+1}$, so $n = m$ and $x = y$. If neither $x$ nor $y$ is a value of $a$, then $x = f(x) = f(y) = y$. If $x = a_n$ and $y$ is not a value of $a$, then $f(y) = y$ and $f(x) = a_{n+1}$, so $y = a_{n+1}$ is a value of $a$, which is false. The map $f$ is not surjective: $a_0$ is not $f(a_n) = a_{n+1}$, since $a$ is injective, and it is not $f(x) = x$ for an $x$ outside the values of $a$. $\square$

::: mathlib
`Infinite.of_injective_to_set` · `Mathlib.Data.Fintype.EquivFin`

Mathlib states the first direction in the form of Dedekind: if `s ≠ Set.univ` and there is an injective `f : α → s`, then `α` is infinite. The map to `s` is an injective self-map whose image misses the points outside `s`. The dual form is `Infinite.of_surjective_from_set`. The second direction has no name of its own, and a proof builds the map from `Infinite.natEmbedding` as above.

<?decl Infinite.of_injective_to_set?>
:::

**Theorem (Bounded sets of natural numbers).** A set $s \subseteq \mathbb{N}$ is finite if and only if it is bounded above.

*Proof.* Assume that $s$ is finite, with the finset $t$. Let $b = \sum_{x \in t} x$. As in the proof that $\mathbb{N}$ is infinite, each $x \in s$ satisfies $x \le b$. So $s$ is bounded above. Conversely, assume that $x \le b$ for each $x \in s$. Then $s \subseteq \{0, 1, \ldots, b\}$, which is the finite set of the $k < b + 1$, and a subset of a finite set is finite. $\square$

So a set of natural numbers is infinite exactly when it has elements beyond each bound: for each $n$ there is an $x \in s$ with $x > n$.

::: mathlib
`Set.infinite_of_not_bddAbove` · `Mathlib.Data.Set.Finite.Lattice`

Mathlib proves the rule for any nonempty directed preorder, not only for `ℕ`: a finite set has an upper bound (`Set.Finite.bddAbove`), so a set with no upper bound is infinite. The converse fails in general, for example in `ℤ` or in `ℝ`, and it holds in `ℕ` because the intervals `{k | k ≤ b}` are finite. The predicate `BddAbove s` is from Volume 4. The form "for each `a` there is a larger element of `s`" is `Set.infinite_of_forall_exists_gt`.

<?decl Set.infinite_of_not_bddAbove?>
:::

**Theorem (Euclid).** The set of the prime numbers is infinite.

*Proof.* By the last theorem it is enough to show that the set is not bounded above: for each $n$ there is a prime $p > n$. Let $N = n! + 1$. Then $N \ge 2$, since $n! \ge 1$. So $N$ has a prime factor $p$, for example its smallest factor larger than $1$. Assume, for a contradiction, that $p \le n$. Then $p$ is one of the factors $1, 2, \ldots, n$ of $n!$, so $p \mid n!$. Also $p \mid N = n! + 1$. So $p$ divides the difference $N - n! = 1$, which is false for a prime. Hence $p > n$. $\square$

::: mathlib
`Nat.infinite_setOfPred_prime` · `Mathlib.Data.Nat.PrimeFin`

The statement is `{p | p.Prime}.Infinite`. The proof in Mathlib is one line: `Set.infinite_of_not_bddAbove` applied to `Nat.not_bddAbove_setOfPred_prime`. The bound comes from `Nat.exists_infinite_primes`, the form "for each `n` there is a prime `p ≥ n`", which Volume 2 proves by the argument above with `Nat.minFac (n ! + 1)`, the smallest prime factor.

<?decl Nat.infinite_setOfPred_prime?>
:::

**Theorem (The counts of an infinite set).** If $s$ is infinite, then $\operatorname{ncard}(s) = 0$ and $\operatorname{encard}(s) = \infty$. Conversely, $\operatorname{encard}(s) = \infty$ implies that $s$ is infinite.

*Proof.* By the definitions of Section 1, $\operatorname{encard}(s)$ is the number of elements when $s$ is finite, a natural number, and $\infty$ when $s$ is infinite. So $\operatorname{encard}(s) = \infty$ exactly when $s$ is infinite. The count $\operatorname{ncard}(s)$ is $\operatorname{encard}(s)$ cut to $\mathbb{N}$, and the cut sends $\infty$ to $0$. $\square$

::: mathlib
`Set.Infinite.ncard` · `Mathlib.Data.Set.Card`

The lemma gives `s.ncard = 0` from `s.Infinite`. With `Set.ncard_eq_zero`, which needs `s.Finite`, it shows that `ncard s = 0` means "empty or infinite". The rule for `encard` is `Set.encard_eq_top_iff`. A proof that needs to tell the two cases apart should use `encard`.

<?decl Set.Infinite.ncard?>
:::

### Examples

**Example (All natural numbers).** The set `Set.univ` of a type with an `Infinite` instance is infinite. For `ℕ` the instance comes from the theorem above.

<?lean MathlibHandbook/V03/C05/Examples.lean#infinite_univ?>

**Example (Primes).** The set of the primes is infinite, by the theorem of Euclid.

<?lean MathlibHandbook/V03/C05/Examples.lean#primes?>

**Example (The numbers of Euclid).** The proof of Euclid gives a prime beyond $n$ for each $n$. For $n = 3$, $3! + 1 = 7$, which is prime. For $n = 4$, $4! + 1 = 25 = 5^2$, and $5 > 4$. For $n = 5$, $5! + 1 = 121 = 11^2$, and $11 > 5$. For $n = 6$, $6! + 1 = 721 = 7 \cdot 103$, and both factors are larger than $6$. The prime is often much larger than $n$, and the proof does not claim that it is the next prime after $n$.

**Example (Multiples and squares).** The set $M$ of the multiples of $12$ is infinite: the map $n \mapsto 12 n$ from $\mathbb{N}$ is injective and has its values in $M$. The set of the squares is infinite: it is not bounded above, since $(b + 1)^2 > b$ for each $b$. The set $\{n : n^2 < 1000\}$ is finite: its elements are at most $31$, since $31^2 = 961$ and $32^2 = 1024$. It has $32$ elements, $0$ to $31$, and its `ncard` is $32$.

**Example (Dedekind maps).** On $\mathbb{N}$, the map $n \mapsto n + 1$ is injective and misses $0$. On $\mathbb{Z}$, the map $n \mapsto 2n$ is injective and misses $1$. On the set $s = \{1, 1/2, 1/3, \ldots\} \cup [2, 3]$ of real numbers, the map of the proof of Dedekind, with $a_n = 1/(n+1)$, sends $1/(n+1)$ to $1/(n+2)$ and fixes each point of $[2, 3]$. It is injective and misses $1$.

**Example (Finsets of each size in ℕ).** The proof of the theorem on finsets of each size, run on $\mathbb{N}$ from $s = \{5, 7\}$ to size $4$ with the choice $m + 1$ of the proof that $\mathbb{N}$ is infinite, adds $5 + 7 + 1 = 13$ and then $5 + 7 + 13 + 1 = 26$. The result is $\{5, 7, 13, 26\}$.

**Counterexample (Bounded and infinite).** In $\mathbb{Z}$, the set of the negative integers is bounded above by $0$, and it is infinite, because $n \mapsto -(n+1)$ from $\mathbb{N}$ is injective with values in it. In $\mathbb{R}$, the interval $[0, 1]$ is bounded and infinite. So the theorem on bounded sets needs $\mathbb{N}$, or another order in which the sets $\{x : x \le b\}$ are finite.

**Counterexample (A surjection from an infinite type).** The map $n \mapsto n \bmod 2$ from $\mathbb{N}$ onto $\{0, 1\}$ is surjective, and the target is finite. So the rule for surjections goes in one direction only: a surjection onto an infinite type makes the domain infinite, not the target.

### Common errors

A learner often tries to prove `s.Infinite` directly from the definition, by an assumption of finiteness and a contradiction. The positive criteria are shorter: an injection from `ℕ` (`Set.infinite_of_injective_forall_mem`), an unbounded set (`Set.infinite_of_not_bddAbove`), or elements beyond each bound (`Set.infinite_of_forall_exists_gt`).

A second error is to use `Set.ncard` for a set that may be infinite. A goal `s.ncard = 0` does not give `s = ∅`, and a sum of `ncard` values can lose the infinite parts. In such a proof, `Set.encard` keeps the information.

A third error is to apply the theorem on bounded sets in `ℤ` or `ℝ`. There, a finite set is bounded, but a bounded set need not be finite.

### The library around it

The file `Mathlib.Data.Fintype.EquivFin` is the home of the class `Infinite` in use: the criteria `Infinite.of_injective`, `Infinite.of_surjective`, `Infinite.of_injective_to_set` and `Infinite.of_surjective_from_set`, the consequences `Infinite.exists_notMem_finset`, `Infinite.exists_subset_card_eq`, `Infinite.exists_superset_card_eq` and `Infinite.natEmbedding`, and the instances for `ℕ` and `ℤ` (`Int.infinite`). The file `Mathlib.Data.Set.Finite.Basic` has the set forms `Set.infinite_univ`, `Set.Infinite.mono`, `Set.Infinite.exists_notMem_finset` and `Set.Infinite.natEmbedding`, and the rule `Set.Finite.infinite_compl`: in an infinite type, the complement of a finite set is infinite. The order forms are in `Mathlib.Data.Set.Finite.Lattice`, with `Set.Finite.bddAbove` and `Set.infinite_of_not_bddAbove`. The reference table lists the declarations of the section.

### Exercises

1. (A) Prove that the set of the odd natural numbers is infinite in two ways: by an injection from $\mathbb{N}$ and by the theorem on bounded sets.
2. (A) Give an injective map $\mathbb{Q} \to \mathbb{Q}$ that is not surjective, and one that is surjective but not injective.
3. (A) Compute the finset of the theorem on finsets of each size for $\mathbb{N}$, from $s = \emptyset$ to size $3$, with the choice $m + 1$.
4. (B) Prove that in an infinite type, the complement of a finite set is infinite.
5. (B) Prove that a set $s \subseteq \mathbb{Z}$ is finite if and only if it is bounded above and below.
6. (B) Prove that there are infinitely many primes of the form $4k + 3$. Hint: a product of numbers of the form $4k + 1$ has the same form, so $4 p_1 \cdots p_r - 1$ has a prime factor of the form $4k + 3$.
7. (B) Prove that $\alpha \oplus \alpha$ is infinite when $\alpha$ is infinite, and that $\alpha \times \beta$ is infinite when $\alpha$ is infinite and $\beta$ is nonempty.
8. (C) Prove that the union of an infinite family of pairwise disjoint nonempty sets is infinite.
9. (C) Prove that an infinite type $\alpha$ is in bijection with $\alpha \oplus \mathrm{Unit}$. Hint: use the map of the proof of Dedekind, and send the new point to $a_0$.

### Notes and history

The proof of the infinitude of the primes is Proposition 20 of Book IX of the *Elements* of Euclid, about 300 BC. Euclid states it as "the primes are more than any given multitude of primes" and uses the product of the given primes plus one, not a factorial. The definition of an infinite set by a bijection with a proper subset is from Dedekind, in *Was sind und was sollen die Zahlen?* (1888). Galileo had noted in 1638 that the squares are in bijection with all natural numbers, and he saw this as a paradox. That a set with no injection from $\mathbb{N}$ can be infinite without choice was shown by Fraenkel and later by Cohen with forcing.

In Mathlib, the class `Infinite` and its criteria come from the Lean 3 library, by Mario Carneiro and others. The names with `not_mem` became names with `notMem` across the library, and the deprecated aliases of the old names were later removed. MIL proves the infinitude of the primes in its chapter on elementary number theory.

### Reference

<?reference?>
