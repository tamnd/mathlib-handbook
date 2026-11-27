---
title: Countable sets and the theorem of Cantor
kind: theory
modules:
  - Mathlib.Data.Set.Countable
explains:
  E3: [Countable, Set.Countable, Set.countable_iUnion]
  E2: [Encodable, Denumerable, Countable.exists_injective_nat, Set.Countable.union, Nat.pair, Cardinal.not_countable_real, Function.cantor_surjective]
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

## Countable sets and the theorem of Cantor

### Overview

A set is countable when its elements can be listed as $x_0, x_1, x_2, \ldots$, perhaps with repetitions or with a finite list. The natural numbers, the integers and the rationals are countable, and the real numbers are not. Countable sets are important in measure theory and topology, because a countable union of null sets is null. Mathlib has three levels: the class `Countable α` is a proposition, the class `Encodable α` gives an injective code in `ℕ` as data, and the class `Denumerable α` gives an equivalence with `ℕ`. For sets, `Set.Countable s` is `Countable s`. This section gives the definitions, the closure rules and the two theorems of Cantor.

### Definitions

**Definition (Countable).** `Countable α` says that there is an injective map `α → ℕ`. A finite type is countable.

**Definition (Countable set).** For `s : Set α`, `s.Countable` is `Countable s`, where `s` is a type by the coercion to a subtype.

**Definition (Encodable and Denumerable).** A term of `Encodable α` has a function `encode : α → ℕ` and a function `decode : ℕ → Option α` with `decode (encode a) = some a`. A term of `Denumerable α` is an encodable type where each number is the code of an element, so it gives an equivalence `Denumerable.eqv α : α ≃ ℕ`.

**Definition (Uncountable).** `Uncountable α` is the class that says `α` is not countable.

### Theorems and proofs

**Theorem (Pairs).** The type `ℕ × ℕ` is countable.

*Proof.* The function `Nat.pair` sends $(a, b)$ to $b^2 + a$ if $a < b$ and to $a^2 + a + b$ if not. The function `Nat.unpair` is a left inverse, so `Nat.pair` is injective. $\square$

**Theorem (Countable unions).** If each set $s_n$ of a sequence is countable, then $\bigcup_n s_n$ is countable.

*Proof.* Choose an injective map $f_n : s_n \to \mathbb{N}$ for each $n$. For $x$ in the union, take the least $n$ with $x \in s_n$, and send $x$ to the code of the pair $(n, f_n(x))$. This map is injective. The proof uses the axiom of choice. $\square$

**Theorem (Cantor).** For each type $\alpha$, no map $f : \alpha \to \mathcal{P}(\alpha)$ is surjective.

*Proof.* Let $D = \{x \mid x \notin f(x)\}$. If $f(a) = D$, then $a \in D$ if and only if $a \notin D$, which is false. $\square$

**Theorem (Real numbers).** The set of the real numbers is not countable.

*Proof.* Mathlib shows that the cardinal of $\mathbb{R}$ is $2^{\aleph_0}$, with a map from the subsets of $\mathbb{N}$ to the real numbers by expansions in base three. By the theorem of Cantor, $2^{\aleph_0} > \aleph_0$. $\square$

::: mathlib
`Countable` · `Mathlib.Basic.Countable.Defs`

The class of the countable types. It is a proposition, so it is the right hypothesis for a theorem. Instances exist for `ℕ`, `ℤ`, `ℚ`, the finite types, and the products, sums, lists and options of countable types.

<?decl Countable?>
:::

::: mathlib
`Set.Countable` · `Mathlib.Data.Set.Countable`

The predicate "the set is countable". The dot notation gives the closure rules: `hs.mono h`, `hs.union ht`, `hs.image f`.

<?decl Set.Countable?>
:::

::: mathlib
`Set.countable_iUnion` · `Mathlib.Data.Set.Countable`

A union over a countable index type of countable sets is countable. The index type needs a `Countable` instance.

<?decl Set.countable_iUnion?>
:::

### Examples

**Example (Instances).**

<?lean MathlibHandbook/V03/C08/Examples.lean#instances?>

**Example (Pairs).**

<?lean MathlibHandbook/V03/C08/Examples.lean#pair?>

**Example (An injective code).**

<?lean MathlibHandbook/V03/C08/Examples.lean#injective?>

**Example (A union).**

<?lean MathlibHandbook/V03/C08/Examples.lean#union?>

**Example (A countable union).**

<?lean MathlibHandbook/V03/C08/Examples.lean#iUnion?>

**Example (The real numbers).**

<?lean MathlibHandbook/V03/C08/Examples.lean#real?>

**Example (Cantor).**

<?lean MathlibHandbook/V03/C08/Examples.lean#cantor?>

**Counterexample (A union over an uncountable index).** Each singleton $\{x\}$ with $x \in \mathbb{R}$ is countable, but the union over all $x$ is $\mathbb{R}$. So `Set.countable_iUnion` needs a countable index type.

### The library around it

`Set.Countable.insert` and `Set.countable_singleton` give the small countable sets. `Set.countable_range` says that the range of a map from a countable type is countable. `Function.Injective.countable` makes a countable type from an injective map to a countable type. `Encodable.encodek` is the equation of the code. `Nat.pairEquiv` is the equivalence of `ℕ × ℕ` with `ℕ`. `Set.to_countable` proves `s.Countable` from an instance. The cardinals of the volume on set theory give the general frame, with `Cardinal.mk_le_aleph0_iff` as the bridge.

### Exercises

1. (A) Give `Nat.pair 2 3` from the definition.
2. (A) Explain why `Countable` is a proposition but `Encodable` is not.
3. (B) Prove that the set of the finite subsets of `ℕ` is countable.
4. (L) Prove that a subset of a countable set is countable. The solution is `countable_mono_example`.
5. (L) Prove that the image of a countable set is countable. The solution is `countable_image_example`.
6. (L) Prove that a set with one element is countable. The solution is `countable_singleton_example`.
7. (L) Prove that the range of a map from `ℕ` is countable. The solution is `countable_range_example`.

### Notes and history

Cantor proved in 1874 that the real numbers are not countable, and he gave the diagonal argument in 1891. The pairing function of `Nat.pair` comes from Szudzik and is different from the function of Cantor, which uses triangle numbers. The proof that a countable union of countable sets is countable needs a weak form of the axiom of choice, and Mathlib uses classical logic for it. MIL shows the diagonal argument in its chapter on sets and functions.

### Reference

<?reference?>
