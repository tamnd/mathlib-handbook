---
title: Pointwise products of finite sets
kind: api
modules:
  - Mathlib.Algebra.Group.Pointwise.Finset.Basic
  - Mathlib.Algebra.Group.Pointwise.Finset.BigOperators
  - Mathlib.Algebra.Group.Pointwise.Finset.Density
  - Mathlib.Algebra.Group.Pointwise.Finset.Interval
  - Mathlib.Algebra.Group.Pointwise.Finset.SelfInv
explains:
  E2: [Finset.card_mul_le, Finset.card_le_card_mul_left, Finset.one_mem_div_iff, Finset.mul_eq_one_iff, Finset.isUnit_iff_singleton, Finset.coe_mul, Finset.card_pow_mono, "Finset.Icc_mul_Icc_subset'"]
  E1: auto
families: []
requires: [V01, V05.C01, V05.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Pointwise products of finite sets

### Overview

Section 1 defines the product $s t$, the inverse $s^{-1}$ and the power $s^n$ for sets $s$ and $t$ of a monoid. This section gives the same operations for finite sets, that is, for terms of `Finset α`. The definitions are the same in mathematics: $s t = \{ a b : a \in s, b \in t \}$. The difference is in the questions. For a finset the cardinality $|s t|$ is a natural number, and additive combinatorics studies how $|s t|$ compares with $|s|$ and $|t|$. This section gives the first bounds of this theory.

The modules follow one plan. `Mathlib.Algebra.Group.Pointwise.Finset.Basic` defines the operations, gives the membership lemmas, the algebraic structure on `Finset α` and the first cardinality bounds. Four small modules add the big operators, the density, the products of intervals and the symmetric finsets. The actions of a group on its finsets, with the translates $a s$, are the subject of Section 4.

### The library around it

#### The operations and the scope

All the operations of this section are scoped instances. They exist only after the command `open Pointwise`, or `open scoped Pointwise`. Without this command, `s * t` for two finsets gives an error, because Lean finds no instance of Mul (Finset α). The scope keeps these instances out of the files that do not need them.

The instances are `Finset.mul`, `Finset.inv`, `Finset.div`, `Finset.one`, `Finset.npow` and `Finset.zpow`, with their additive versions. Each operation is an image. The definition lemmas show this:

| Lean name | Statement |
| --- | --- |
| `Finset.mul_def` | $s t$ is the image of $s \times t$ under $(a, b) \mapsto a b$ |
| `Finset.inv_def` | $s^{-1}$ is the image of $s$ under $a \mapsto a^{-1}$ |
| `Finset.div_def` | $s / t$ is the image of $s \times t$ under $(a, b) \mapsto a / b$ |
| `Finset.singleton_one` | $\{1\} = 1$ |

An image of finsets needs a decidable equality on the target, because `Finset.image` must remove the duplicates. So most lemmas of this section have the hypothesis `[DecidableEq α]`. The unit `1 : Finset α` is the singleton $\{1\}$, and it needs no decidability.

The membership lemmas are the main tool for proofs. The lemma `Finset.mem_mul` states $x \in s t \iff \exists y \in s, \exists z \in t, y z = x$, and `Finset.mem_inv'` states $a \in s^{-1} \iff a^{-1} \in s$ when the inverse is involutive. The lemmas `Finset.mul_mem_mul` and `Finset.inv_mem_inv` give the easy direction. For powers, `Finset.mem_pow` writes an element of $s^n$ as a product of a list of $n$ elements of $s$, given by a function on `Fin n`.

#### The link with sets

The coercion from `Finset α` to `Set α` respects every operation. The lemmas `Finset.coe_mul`, `Finset.coe_inv`, `Finset.coe_div`, `Finset.coe_one`, `Finset.coe_pow` and `Finset.coe_zpow` state this, and they are simp lemmas. So the identity $\uparrow(s t) = \uparrow s \cdot \uparrow t$ moves a problem about finsets to Section 1. The proof is the extensionality of sets and `Finset.mem_mul` on the left with `Set.mem_mul` on the right. For a monoid, `Finset.coeMonoidHom` packs the coercion as a monoid homomorphism `Finset α →* Set α`. In the other direction, `Set.toFinset_mul` and `Set.Finite.toFinset_mul` compute the finset of a finite product of sets.

#### The structure on finsets

With the pointwise product, `Finset α` is a monoid when $\alpha$ is a monoid, by `Finset.monoid`, and commutative when $\alpha$ is commutative, by `Finset.commMonoid`. For a group $\alpha$, `Finset α` is not a group: the product $s s^{-1}$ contains $1$ and has more than one element when $s$ has more than one element. The structure is a division monoid, by `Finset.divisionMonoid`. In this structure the units are few.

**Theorem.** Let $\alpha$ be a division monoid. Then $s t = 1$ if and only if $s = \{a\}$ and $t = \{b\}$ with $a b = 1$. This is `Finset.mul_eq_one_iff`.

*Proof sketch.* If $s t = \{1\}$, then both $s$ and $t$ are nonempty. For $a, a' \in s$ and $b \in t$, both $a b$ and $a' b$ are $1$. In a division monoid $a b = 1$ gives $a = b^{-1}$, so $a = a'$. Thus $s$ is a singleton, and $t$ also by the same argument. The converse is `Finset.singleton_mul_singleton`.

So in a group the units of `Finset α` are exactly the singletons: `Finset.isUnit_iff_singleton` states $\mathrm{IsUnit}(s) \iff \exists a, s = \{a\}$. The map $a \mapsto \{a\}$ is a monoid homomorphism `Finset.singletonMonoidHom`, and `Finset.imageMonoidHom` sends a homomorphism $f$ to the homomorphism $s \mapsto f(s)$ of finsets. The lemma `Finset.image_mul` states $f(s t) = f(s) f(t)$ for a multiplicative map $f$.

The empty finset absorbs the product: `Finset.empty_mul` and `Finset.mul_empty`. The lemma `Finset.mul_nonempty` states that $s t$ is nonempty if and only if $s$ and $t$ are nonempty. The product distributes over unions, by `Finset.mul_union` and `Finset.union_mul`, but only an inclusion holds for intersections. In a finite monoid, `Finset.univ_mul_univ` states that the whole finset is idempotent, and `Finset.univ_pow` gives the same for powers with $n \ne 0$.

#### Cardinality bounds

The first bounds come from the definition as an image.

**Theorem.** $|s t| \le |s| \, |t|$. This is `Finset.card_mul_le`.

*Proof.* The finset $s t$ is the image of $s \times t$. An image has at most as many elements as the source, by `Finset.card_image_le`, and $|s \times t| = |s| \, |t|$ by `Finset.card_product`.

Equality holds if and only if the product map is injective on $s \times t$, by `Finset.card_mul_iff`. The same bound holds for division, by `Finset.card_div_le`, and for powers: `Finset.card_pow_le` states $|s^n| \le |s|^n$.

**Theorem.** If multiplication is left cancellative and $s$ is nonempty, then $|t| \le |s t|$. This is `Finset.card_le_card_mul_left`.

*Proof.* Take $a \in s$. Left multiplication by $a$ is injective, so the finset $a t$ has $|t|$ elements. Each element $a b$ with $b \in t$ is in $s t$, so $a t \subseteq s t$, and `Finset.card_le_card` gives the bound.

The lemma `Finset.card_le_card_mul_right` is the version with right cancellation, and `Finset.card_le_card_mul_self` gives $|s| \le |s s|$. With a cancellative monoid the powers of a nonempty finset grow: `Finset.card_pow_mono` states $|s^m| \le |s^n|$ for $1 \le m \le n$. When $1 \in s$, the finsets themselves grow, $s^m \subseteq s^n$, by `Finset.pow_right_monotone`. The lemma `Finset.card_inv` states $|s^{-1}| = |s|$, since the inverse is a bijection.

For a group, the quotient $s / t$ detects common elements.

**Theorem.** In a group, $1 \in s / t$ if and only if $s$ and $t$ are not disjoint. This is `Finset.one_mem_div_iff`.

*Proof.* An element of $s / t$ is $b / c$ with $b \in s$ and $c \in t$, and $b / c = 1$ if and only if $b = c$.

The lemma `Finset.one_notMem_div_iff` is the negation. The pair `Finset.one_mem_inv_mul_iff` and `Finset.one_notMem_inv_mul_iff` give the same statement for $t^{-1} s$.

#### Big operators, sup and inf

The module `Mathlib.Algebra.Group.Pointwise.Finset.BigOperators` has two results. The lemma `Finset.coe_prod` states that the coercion to sets respects a finite product of finsets, in a commutative monoid. The lemma `Finset.prod_inv_index` reindexes a product over $s^{-1}$: $\prod_{i \in s^{-1}} f(i) = \prod_{i \in s} f(i^{-1})$. The additive names are `Finset.coe_sum` and `Finset.sum_inv_index`. In the basic module, the supremum and the infimum of a function over a product split into two steps, by `Finset.sup_mul_left` and `Finset.inf_mul_left`, and `Finset.sup_mul_le` states $\sup_{s t} f \le a$ if and only if $f(x y) \le a$ for all $x \in s$ and $y \in t$.

#### Density, intervals and symmetric finsets

In a finite type the density of $s$ is $|s|$ divided by the size of the type, the function `Finset.dens`. The module `Mathlib.Algebra.Group.Pointwise.Finset.Density` states that the inverse and the translates keep the density: `Finset.dens_inv`, `Finset.dens_smul_finset`, and the additive `Finset.dens_neg` and `Finset.dens_vadd_finset`.

The module `Mathlib.Algebra.Group.Pointwise.Finset.Interval` gives products of finite intervals in an ordered monoid with a locally finite order. The lemma `Finset.Icc_mul_Icc_subset'` states $[a, b] \cdot [c, d] \subseteq [a c, b d]$ when multiplication is monotone on both sides. The proof is one line: if $a \le x \le b$ and $c \le y \le d$, then $a c \le x y \le b d$. The other lemmas treat the open and half open intervals, where strict monotonicity is needed. The additive lemmas have no prime, for example `Finset.Icc_add_Icc_subset`, and the multiplicative lemmas end with a prime.

The module `Mathlib.Algebra.Group.Pointwise.Finset.SelfInv` treats finsets with $s^{-1} = s$. The lemma `Finset.isSelfInv_iff_forall_inv_mem` states that this holds if and only if $s$ is closed under the inverse, and `Finset.isSelfInv_coe_iff` moves the property to the set $\uparrow s$. The additive names use `IsSelfNeg`, for example `Finset.isSelfNeg_iff_forall_neg_mem`.

#### Common errors

1. A learner writes `s * t` for two finsets and gets an error that no instance of Mul exists. The pointwise instances are scoped: add `open Pointwise` at the top of the file.
2. For finsets, `n • s` is the sum $s + s + \cdots + s$ of $n$ copies, not the dilation $\{n x : x \in s\}$. The finset $2 • \{0, 1\}$ in $\mathbb{Z}$ is $\{0, 1, 2\}$. The dilation is the image of $s$ under $x \mapsto n x$.
3. Most lemmas need `[DecidableEq α]`. In a classical proof, two different decidability instances can give two terms for the same product finset that are not equal by definition. Use the tactic convert or the `Finset.coe_mul` lemma to compare them.

### Exercises

1. (A) In $\mathbb{Z}$, compute $s + s$ for $s = \{0, 1, 3\}$. Compare $|s + s|$ with the bound of `Finset.card_mul_le` and with the bound $|s| \le |s + s|$.
2. (A) Show that $|s t| = |s|$ when $t = \{a\}$ in a group, with `Finset.card_mul_singleton`, and give an example in a monoid that is not cancellative where $|s \{a\}| < |s|$.
3. (B) Let $G$ be a finite group and $s, t$ finsets with $|s| + |t| > |G|$. Show that $s t = G$. Hint: for $g \in G$, the finsets $s$ and $g t^{-1}$ have a common element.
4. (B) In a finite group, let $s$ be a nonempty finset with $s s \subseteq s$. Show that $s$ is a subgroup. Hint: for $a \in s$ the map $x \mapsto a x$ sends $s$ into $s$ and is injective.
5. (B) Use `Finset.mul_eq_one_iff` to show that $\{1, a\}$ is not a unit of `Finset G` when $a \ne 1$.
6. (C) Let $s$ be a finset of a group $G$ with $1 \in s$ and $|s s| = |s|$. Show that $s$ is a subgroup of $G$. Hint: $s \subseteq s s$ by `Finset.pow_right_monotone`, so $s s = s$.

### Reference

<?reference?>
