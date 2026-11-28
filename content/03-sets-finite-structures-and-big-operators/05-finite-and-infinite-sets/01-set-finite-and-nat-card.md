---
title: Set.Finite, Finite and Nat.card
kind: theory
modules:
  - Mathlib.Data.Set.Finite.Basic
  - Mathlib.Basic.Finite.Defs
  - Mathlib.Data.Set.Card
  - Mathlib.Basic.Finite.Prod
  - Mathlib.Basic.Finite.Set
  - Mathlib.Basic.Finite.Sigma
  - Mathlib.Basic.Finite.Sum
  - Mathlib.Data.Finite.Card
  - Mathlib.Data.Finite.Defs
  - Mathlib.Data.Finite.Prod
  - Mathlib.Data.Finite.Set
  - Mathlib.Data.Finite.Sigma
  - Mathlib.Data.Finite.Sum
  - Mathlib.Data.Finite.Vector
explains:
  E3: [Set.Finite, Nat.card]
  E2: [Set.Infinite, Finite, Set.ncard, Set.Finite.subset, Set.Finite.toFinset, Set.Finite.union, Set.Finite.image, Set.encard, Set.ncard_union_add_ncard_inter, Finite.of_injective, Finite.of_surjective, Set.finite_coe_iff, Fintype.ofFinite, Set.Finite.induction_on]
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

## Set.Finite, Finite and Nat.card

### Overview

The class `Fintype` of Chapter 4 is data: it holds a finset of all the elements. In a proof that data is often not available, and often it is not needed. The set of the real roots of a nonzero polynomial is finite, but no program lists the roots of a real polynomial. The set of the units of a finite ring is finite, and a proof of this should not depend on an algorithm. For such statements the textbook notion is the right one: a set is finite when it is in bijection with $\{0, 1, \ldots, n-1\}$ for some $n$.

Mathlib has this notion as the class `Finite α` for a type and as the predicate `Set.Finite s` for a set. Their negations are `Infinite α` and `Set.Infinite s`. This section gives the definitions, proves that they agree with the finsets of Chapter 3, proves the closure rules (subsets, unions, images, products, preimages) and gives the three counts `Nat.card`, `Set.ncard` and `Set.encard`, which need no instance. After the section the reader can prove that a set is finite from the way it is built, and can count it with the right function. Section 2 treats the infinite sets.

### Definitions

**Definition (Finite type).** A type $\alpha$ is *finite* if there are a natural number $n$ and a bijection $\alpha \to \{0, 1, \ldots, n - 1\}$.

The number $n$ is unique: two bijections $\alpha \to \mathrm{Fin}\ n$ and $\alpha \to \mathrm{Fin}\ m$ give a bijection $\mathrm{Fin}\ n \to \mathrm{Fin}\ m$, and then $n = m$ by the card rule for equivalent types of Chapter 4. The definition states only that a bijection exists. It does not choose one.

::: mathlib
`Finite` · `Mathlib.Basic.Finite.Defs`

`Finite α` is a class with one constructor, `Finite.intro`, that takes an equivalence `α ≃ Fin n`. The class is a proposition, so two proofs of it are equal by definition. This is the main difference with `Fintype α`, which is data and has instances that can differ as terms. The class is stated for any `Sort`, so it applies to propositions too. `Finite.exists_equiv_fin` gives back the `n` and the equivalence, in a `Nonempty`, because a proposition does not hold data.

<?decl Finite?>
:::

**Definition (Finite set).** A set $s \subseteq \alpha$ is *finite* if the type of its elements is finite. It is *infinite* if it is not finite.

::: mathlib
`Set.Finite` · `Mathlib.Basic.Finite.Defs`

The definition is `protected def Set.Finite (s : Set α) : Prop := Finite s`, where `s` stands for the subtype `{x // x ∈ s}`. The lemma `Set.finite_coe_iff` turns `Finite s` into `s.Finite` and back. `Set.toFinite s` proves `s.Finite` from an instance `Finite s`, for example when `s` lives in a finite type. The dot notation gives the closure rules of this section: `hs.subset h`, `hs.union ht`, `hs.image f`. `Set.Infinite s` is the definition `¬ s.Finite`.

<?decl Set.Finite?>
:::

**Definition (The counts).** For a type $\alpha$, $\operatorname{Nat.card}(\alpha)$ is the number of elements of $\alpha$ when $\alpha$ is finite, and $0$ when $\alpha$ is infinite. For a set $s$, $\operatorname{ncard}(s) = \operatorname{Nat.card}(s)$. The *extended card* $\operatorname{encard}(s)$ is the number of elements in $\mathbb{N} \cup \{\infty\}$, with the value $\infty$ for an infinite set.

The value $0$ for an infinite type is a convention. It makes `Nat.card` a total function, in the way that $x / 0 = 0$ makes the division total. The price is that a lemma about `Nat.card` or `ncard` often needs a hypothesis of finiteness. The count `encard` has no junk value, so its lemmas hold with no hypothesis.

::: mathlib
`Nat.card` · `Mathlib.SetTheory.Cardinal.Finite`

`Nat.card α` is defined from the cardinal number of `α` (Volume 31), cut to `ℕ`, and the cut sends an infinite cardinal to `0`. The user rarely needs this. `Nat.card_eq_fintype_card` gives `Fintype.card α` when there is an instance, and `Nat.card_eq_zero_of_infinite` gives `0` for an infinite type. In the file `Mathlib.Data.Set.Card`, `Set.encard s` has values in `ℕ∞`, and `Set.ncard s` is defined as `ENat.toNat s.encard`, which sends `⊤` to `0`.

<?decl Nat.card?>
:::

### Theorems and proofs

**Theorem (Finite types and finite type structures).** A type with a finite type structure in the sense of Chapter 4 is finite. Conversely, a finite type has a finite type structure.

*Proof.* Let $U$ be a finset that contains every element of $\alpha$, and let $|U| = n$. A finset is a list with no repetition, up to order. Take such a list $a_0, \ldots, a_{n-1}$. The map $i \mapsto a_i$ from $\mathrm{Fin}\ n$ to $\alpha$ is injective, because the list has no repetition, and surjective, because each element of $\alpha$ is in $U$. Its inverse is a bijection $\alpha \to \mathrm{Fin}\ n$. Conversely, let $e : \alpha \to \mathrm{Fin}\ n$ be a bijection. The image of the finset of all elements of $\mathrm{Fin}\ n$ under $e^{-1}$ is a finset of $\alpha$, and it contains each $x$, since $x = e^{-1}(e(x))$. $\square$

The converse needs the bijection $e$ as data, and the definition of finiteness gives it only as an existence statement. So the finset is a choice, and the construction is not computable.

::: mathlib
`Fintype.ofFinite` · `Mathlib.Data.Fintype.EquivFin`

The two directions are `Finite.of_fintype`, an instance, and `Fintype.ofFinite`, a noncomputable definition. The library advice is to write `have := Fintype.ofFinite α` inside a proof that needs a finset, and never to make `Fintype.ofFinite` a global instance, because it would give a second instance that does not compute and that is not equal by definition to the computable one.

<?decl Fintype.ofFinite?>
:::

**Theorem (Finite sets and finsets).** A set $s \subseteq \alpha$ is finite if and only if there is a finset $t$ with the same elements as $s$. This finset is unique.

*Proof.* If $s$ is finite, the type of its elements has a finite type structure $U$ by the last theorem. The image of $U$ under the inclusion of $s$ in $\alpha$ is a finset $t$ of $\alpha$. An element $x \in \alpha$ is in $t$ exactly when $x$ is the image of an element of $s$, that is, when $x \in s$. Conversely, let $t$ have the same elements as $s$. The elements of $t$ that lie in $s$ form a finite type structure on the type of the elements of $s$, so $s$ is finite. Two finsets with the same elements are equal, so $t$ is unique. $\square$

::: mathlib
`Set.Finite.toFinset` · `Mathlib.Data.Set.Finite.Basic`

`hs.toFinset` is the finset of the theorem, for a proof `hs : s.Finite`. Its two main lemmas are `Set.Finite.mem_toFinset`, the membership, and `Set.Finite.coe_toFinset`, which says that the coercion back to a set is `s`. With it, a proof that starts with a finite set can use the finset tools of Chapter 3: the card, the induction and the sums. In the other direction, a finset `t` gives the finite set `(t : Set α)` with the proof `t.finite_toSet`.

<?decl Set.Finite.toFinset?>
:::

**Theorem (Injections and surjections).** Let $f : \alpha \to \beta$. If $\beta$ is finite and $f$ is injective, then $\alpha$ is finite. If $\alpha$ is finite and $f$ is surjective, then $\beta$ is finite.

*Proof.* First part. Let $e : \beta \to \mathrm{Fin}\ n$ be a bijection. The map $e \circ f : \alpha \to \mathrm{Fin}\ n$ is injective. Its image $S$ is a subset of $\mathrm{Fin}\ n$, so $S$ is a finset, with $m$ elements, say. The map $e \circ f$ is a bijection from $\alpha$ onto $S$, and $S$ is in bijection with $\mathrm{Fin}\ m$ by the first theorem. So $\alpha$ is in bijection with $\mathrm{Fin}\ m$.

Second part. For each $y \in \beta$ choose $g(y) \in \alpha$ with $f(g(y)) = y$. Then $g$ is injective, as in the proof of the theorem on injective and surjective maps in Chapter 4. By the first part, $\beta$ is finite. $\square$

::: mathlib
`Finite.of_injective` · `Mathlib.Data.Fintype.EquivFin`

The finite type is an instance argument `[Finite β]`, and the map and the proof of injectivity are explicit. `Finite.of_surjective` is the second part. Most closure rules for sets are proved from these two rules. The contrapositive forms for infinite types, `Infinite.of_injective` and `Infinite.of_surjective`, are in Section 2.

<?decl Finite.of_injective?>
:::

**Theorem (Closure rules).** Let $s, t \subseteq \alpha$ and $f : \alpha \to \beta$.

1. If $t$ is finite and $s \subseteq t$, then $s$ is finite.
2. If $s$ and $t$ are finite, then $s \cup t$ is finite.
3. If $s$ is finite, then $s \cap u$ and $s \setminus u$ are finite for every set $u$.
4. If $s$ is finite, then $f(s)$ is finite.
5. If $s \subseteq \alpha$ and $t \subseteq \beta$ are finite, then $s \times t$ is finite.
6. If $s \subseteq \beta$ is finite and $f$ is injective on $f^{-1}(s)$, then $f^{-1}(s)$ is finite.
7. If $s$ is finite, then the set of all subsets of $s$ is finite.

*Proof.* (1) The inclusion of $s$ in $t$ is injective, so the first part of the last theorem applies. (2) Let $s$ and $t$ have the finsets $s'$ and $t'$. The finset $s' \cup t'$ has the same elements as $s \cup t$. (3) The sets $s \cap u$ and $s \setminus u$ are subsets of $s$, so (1) applies. (4) The map $x \mapsto f(x)$ from $s$ onto $f(s)$ is surjective, so the second part of the last theorem applies. (5) The finset $s' \times t'$ of Chapter 3 has the same elements as $s \times t$. (6) The map $x \mapsto f(x)$ from $f^{-1}(s)$ to $s$ is injective by the hypothesis, and $s$ is finite. (7) The power set of the finset $s'$ is a finset, and its elements are the subsets of $s$, one for each subset. $\square$

The rules cover each construction except the infinite union and the preimage by a map that is not injective. Both can make a finite set infinite, as the examples show. A finite union of finite sets is finite, by induction on the number of sets with rule (2). Mathlib states it as `Set.Finite.biUnion`.

::: mathlib
`Set.Finite.subset` · `Mathlib.Data.Set.Finite.Basic`

The rules have the names `Set.Finite.subset`, `Set.Finite.union`, `Set.Finite.inter_of_left`, `Set.Finite.sdiff`, `Set.Finite.image`, `Set.Finite.prod`, `Set.Finite.preimage` and `Set.Finite.powerset`. With the dot notation, a proof reads like the construction of the set: `(hs.union ht).subset h` for a subset of a union. The rule `Set.finite_union` is the form with `↔`. The rule for preimages takes the injectivity as `Set.InjOn f (f ⁻¹' s)`, injectivity on the preimage only.

<?decl Set.Finite.subset?>
:::

**Theorem (Induction on finite sets).** Let $P$ be a property of sets. Assume that $P(\emptyset)$ holds, and that $P(s)$ implies $P(s \cup \{a\})$ for each finite set $s$ and each $a \notin s$. Then $P(s)$ holds for each finite set $s$.

*Proof.* Use induction on $n = \operatorname{ncard}(s)$. If $n = 0$, then $s$ is a finite set with no element, so $s = \emptyset$. If $\operatorname{ncard}(s) = n + 1$, pick $a \in s$ and put $s_0 = s \setminus \{a\}$. Then $s_0$ is finite with $n$ elements, $a \notin s_0$, and $s = s_0 \cup \{a\}$. By the induction hypothesis $P(s_0)$ holds, so $P(s)$ holds. $\square$

::: mathlib
`Set.Finite.induction_on` · `Mathlib.Data.Set.Finite.Basic`

The motive takes the set and the proof of finiteness. In a proof one writes `induction s, hs using Set.Finite.induction_on`, and the two goals are the empty set and the insert of a new element. The proof in Mathlib goes through the finset `hs.toFinset` and `Finset.induction_on` of Chapter 3.

<?decl Set.Finite.induction_on?>
:::

**Theorem (Inclusion and exclusion for ncard).** If $s$ and $t$ are finite, then $\operatorname{ncard}(s \cup t) + \operatorname{ncard}(s \cap t) = \operatorname{ncard}(s) + \operatorname{ncard}(t)$. For the extended card the rule $\operatorname{encard}(s \cup t) + \operatorname{encard}(s \cap t) = \operatorname{encard}(s) + \operatorname{encard}(t)$ holds for all sets.

*Proof.* For finite $s$ and $t$, all four sets are finite by the closure rules, and each count is the card of the finset of the set. The finset of $s \cup t$ is the union of the finsets of $s$ and $t$, and the same holds for the intersection. So the rule is the rule of Chapter 3 for finsets. For the extended card, if $s$ and $t$ are finite this is the same rule. If one of them, say $s$, is infinite, then $s \cup t \supseteq s$ is infinite. Both sides contain a term $\infty$, and $\infty + x = \infty$ for each $x$. So both sides are $\infty$. $\square$

::: mathlib
`Set.ncard_union_add_ncard_inter` · `Mathlib.Data.Set.Card`

The two hypotheses of finiteness are `autoParam` arguments: Lean tries to prove them by the tactic `toFinite_tac`, which works when the type has a `Finite` instance. In a type such as `ℕ` the user gives them. The form for the extended card, `Set.encard_union_add_encard_inter`, has no hypothesis. A proof that mixes finite and infinite sets is often easier with `encard`, and ends with a translation to `ncard`.

<?decl Set.ncard_union_add_ncard_inter?>
:::

### Examples

**Example (Numbers below n).** The set $\{k \in \mathbb{N} : k < n\}$ is finite: the finset `Finset.range n` has the same elements.

<?lean MathlibHandbook/V03/C05/Examples.lean#finite_lt?>

**Example (A subset of a union).** If $s$ and $t$ are finite and $u \subseteq s \cup t$, then $u$ is finite, by rules (2) and (1).

<?lean MathlibHandbook/V03/C05/Examples.lean#subset_union?>

**Example (An image).** The image of a finite set of natural numbers under any map to $\mathbb{Z}$ is finite, by rule (4).

<?lean MathlibHandbook/V03/C05/Examples.lean#image?>

**Example (A set defined by an inequality).** Let $s = \{k \in \mathbb{N} : k^2 < 50\}$. If $k \ge 8$ then $k^2 \ge 64 > 50$, so $s \subseteq \{k : k < 8\}$, and $s$ is finite by rule (1). In fact $7^2 = 49 < 50$, so $s = \{0, 1, \ldots, 7\}$ and $\operatorname{ncard}(s) = 8$. The proof of finiteness used a bound, not the exact set.

**Example (Nat.card of a finite type).** For a type with a `Fintype` instance, `Nat.card` is `Fintype.card`, and `simp` computes it.

<?lean MathlibHandbook/V03/C05/Examples.lean#nat_card?>

**Example (The card of a set).** $\operatorname{ncard}(\{1, 2, 3\}) = 3$. The proof turns the set into a finset with `Set.ncard_eq_toFinset_card'` and counts the finset.

<?lean MathlibHandbook/V03/C05/Examples.lean#ncard?>

**Example (Divisors).** The set $D$ of the positive divisors of $12$ is a subset of $\{k : k < 13\}$, so it is finite. Its elements are $1, 2, 3, 4, 6, 12$, and $\operatorname{ncard}(D) = 6$. The set of the positive multiples of $12$ is infinite: Section 2 proves that a set of natural numbers with no upper bound is infinite.

**Counterexample (A preimage of a finite set).** Let $f : \mathbb{N} \to \mathbb{N}$, $f(n) = n \bmod 2$. The set $\{0\}$ is finite, but $f^{-1}(\{0\})$ is the set of the even numbers, which is infinite. So rule (6) needs the injectivity. In the other direction, the image of the infinite set $\mathbb{N}$ under $f$ is $\{0, 1\}$, which is finite. An image can be finite when the set is not.

**Counterexample (The junk value).** Let $s = \{0\}$ and $t = \mathbb{N}$. Then $s \subseteq t$, but $\operatorname{ncard}(s) = 1$ and $\operatorname{ncard}(t) = 0$. So the monotonicity $\operatorname{ncard}(s) \le \operatorname{ncard}(t)$ fails without the hypothesis that $t$ is finite, and `Set.ncard_le_ncard` has it. Let $s$ be the set of the even numbers and $t = \{1\}$. Then $\operatorname{ncard}(s \cup t) + \operatorname{ncard}(s \cap t) = 0 + 0$, but $\operatorname{ncard}(s) + \operatorname{ncard}(t) = 0 + 1$. So the rule of inclusion and exclusion for `ncard` needs its hypotheses too. With `encard` both sides are $\infty$.

### Common errors

A learner often proves `s.Finite` by hand when the type is finite. If `α` has a `Finite` instance, each `s : Set α` is finite, and `Set.toFinite s` is the proof.

A second error is to use `Set.Finite.toFinset` and then to forget the proof `hs` in the goal. The finset `hs.toFinset` depends on `hs`, but by proof irrelevance it does not depend on which proof, so `rfl` or `simp` removes a mismatch.

A third error is to read `Set.ncard s = 0` as "the set is empty". It means "the set is empty or infinite". The lemma `Set.ncard_eq_zero` has the hypothesis `s.Finite`.

### The library around it

The file `Mathlib.Basic.Finite.Defs` has the classes `Finite` and `Infinite`, the predicates `Set.Finite` and `Set.Infinite`, and the translation lemmas `Set.finite_coe_iff`, `Set.infinite_coe_iff` and `not_finite_iff_infinite`. The file `Mathlib.Data.Set.Finite.Basic` has the closure rules, the instances `Finite` for the subtypes of the constructions (so that `Set.toFinite` proves the finiteness of a union of two finite sets in a finite type), the conversions `Set.Finite.toFinset` and `Set.Finite.exists_finset_coe`, and the base sets `Set.finite_empty`, `Set.finite_singleton` and `Set.Finite.insert`. The rules for indexed unions are in `Mathlib.Data.Set.Finite.Lattice`: `Set.finite_iUnion` for a union indexed by a finite type, and `Set.Finite.biUnion`, `Set.Finite.sUnion`. The file `Mathlib.Data.Set.Card` has the API of `Set.encard` and `Set.ncard`: the insert rule `Set.ncard_insert_of_notMem`, the order rule `Set.ncard_le_ncard`, `Set.ncard_coe_finset` for a finset, and `Set.ncard_eq_toFinset_card` for the passage to a finset. Most of its lemmas have an `autoParam` hypothesis of finiteness. The reference table lists the declarations of the section.

The file `Mathlib.Basic.Finite.Prod` gives the finiteness of products of sets. The rule `Set.Finite.prod` says that $s \times t$ is finite when $s$ and $t$ are finite, and `Set.Finite.toFinset_prod` computes its finset as the product of the two finsets. The converse needs care with the empty set: `Set.finite_prod` says that $s \times t$ is finite exactly when each factor is finite or the other factor is empty, because $s \times \emptyset = \emptyset$ for each $s$. The same idea gives `Set.infinite_prod` and the one-sided rules `Set.Finite.of_prod_left` and `Set.Infinite.prod_left`, each with a hypothesis `Nonempty` on the other factor. For types, `Prod.finite_iff` and the instances `Finite.prod_left` and `Finite.prod_right` play the same role. The rule `Set.Finite.image2` covers the image of $s \times t$ under a map of two arguments, and `Set.Finite.offDiag` covers the pairs $(a, b)$ of $s$ with $a \ne b$. The small files `Mathlib.Basic.Finite.Sigma` and `Mathlib.Basic.Finite.Sum` give `Set.Finite.sigma` for a dependent product of sets, and `Finite.sum_left` and `Finite.sum_right`, which recover the finiteness of $\alpha$ and $\beta$ from that of $\alpha \oplus \beta$. The file `Mathlib.Basic.Finite.Set` gives `Finite.Set.finite_of_finite_image`: a set is finite when its image under a map that is injective on it is finite. The files `Mathlib.Data.Finite.Card`, `Mathlib.Data.Finite.Defs`, `Mathlib.Data.Finite.Prod`, `Mathlib.Data.Finite.Set`, `Mathlib.Data.Finite.Sigma`, `Mathlib.Data.Finite.Sum` and `Mathlib.Data.Finite.Vector` are deprecated modules with no declarations. Each one only imports the new file: `Mathlib.Basic.Finite.Defs` and its neighbours for most of them, `Mathlib.Data.Fintype.Vector` for the vectors, and `Mathlib.SetTheory.Cardinal.NatCard`, a file of the volume on set theory, for `Mathlib.Data.Finite.Card`. A new file imports the new path.

### Exercises

1. (A) Give `Nat.card ℕ`, `Set.ncard (Set.univ : Set ℕ)` and `Set.encard (Set.univ : Set ℕ)`.
2. (A) Explain why `Finite α` is a proposition but `Fintype α` is not, and what this changes for two instances of each.
3. (A) Prove that $\{n \in \mathbb{N} : n \mid 100\}$ is finite, and compute its `ncard`.
4. (B) Prove that the set of the pairs $(a, b) \in \mathbb{N}^2$ with $a + b \le 10$ is finite, by rule (5), and compute its `ncard`. Hint: count the pairs with $a + b = k$ for each $k$.
5. (B) Prove that a finite union $s_1 \cup \cdots \cup s_n$ of finite sets is finite, by induction on $n$.
6. (B) Find sets $s \subseteq t$ with $t$ infinite and $\operatorname{ncard}(t \setminus s) \ne \operatorname{ncard}(t) - \operatorname{ncard}(s)$.
7. (L) Prove that the intersection with a finite set is finite. The solution is `finite_inter_example`.
8. (L) Prove that a set that contains an infinite set is infinite. The solution is `infinite_mono_example`.
9. (L) Prove that a map from a finite type to itself is injective if and only if it is surjective. The solution is `injective_surjective_example`.
10. (L) Prove that a type with an injective map from `ℕ` is infinite. The solution is `infinite_of_injective_example`.

### Notes and history

The definition of a finite set by a bijection with $\{1, \ldots, n\}$ is the one of Cantor and of the textbooks. Dedekind, in *Was sind und was sollen die Zahlen?* (1888), took the other route: a set is infinite when it is in bijection with a proper subset of itself. The two definitions agree under the axiom of countable choice, and Section 2 proves this. The extended card $\operatorname{encard}$ is the cardinal number of Cantor, cut at the first infinite cardinal.

In the Lean 3 library, `Set.Finite` was first an inductive predicate with a `Fintype` instance as its field. Kyle Miller added the class `Finite` in 2022, and later `Set.Finite s` became the statement `Finite s`. So the class `Finite`, in the file `Mathlib.Basic.Finite.Defs`, is now the base of the theory. The file `Mathlib.Data.Set.Card` with `encard` and `ncard` is by Peter Nelson, who wrote it for the theory of matroids, where infinite sets are common and a total count with good lemmas helps. MIL uses `Set.Finite` in its chapter on sets and functions.

### Reference

<?reference?>
