---
title: Pointwise actions on finite sets
kind: api
modules:
  - Mathlib.Algebra.Group.Pointwise.Finset.Scalar
  - Mathlib.Algebra.Group.Action.Pointwise.Finset
explains:
  E2: [Finset.biUnion_smul_finset, Finset.card_smul_finset, Finset.smul_finset_inter, Finset.inv_smul_mem_iff, Finset.singleton_mul, Finset.mul_singleton, Finset.smul_univ, Finset.card_dvd_card_smul_right]
  E1: auto
families: []
requires: [V01, V05.C01, V05.C04, V05.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Pointwise actions on finite sets

### Overview

Section 2 lets a group act on the sets of a type. This section does the same for finite sets. Let $\alpha$ act on $\beta$. For $a \in \alpha$ and a finset $t$ of $\beta$, the translate $a \cdot t$ is the finset $\{a \cdot x : x \in t\}$. For a finset $s$ of $\alpha$, the product $s \cdot t$ is the finset $\{a \cdot x : a \in s, x \in t\}$. When $\alpha$ acts on itself by multiplication, the translate $a \cdot t$ is the left coset $a t$ of Section 3, and the product $s \cdot t$ is the product $s t$.

The module `Mathlib.Algebra.Group.Pointwise.Finset.Scalar` defines the operations and gives their elementary lemmas, for any scalar multiplication. The module `Mathlib.Algebra.Group.Action.Pointwise.Finset` adds the results that need an action or a cancellation law: the translates are actions, they keep the cardinality, and they commute with the Boolean operations. With a group action, the translates give a short proof of a divisibility of cardinalities that contains the theorem of Lagrange of Chapter 4.

### The library around it

#### The operations

The instances are scoped, as in Section 3. They exist only after `open Pointwise`. The module defines four binary operations and one translation:

| Lean name | Operation |
| --- | --- |
| `Finset.smul` | $s \cdot t = \{a \cdot x : a \in s, x \in t\}$ for $s$ in $\alpha$ and $t$ in $\beta$ |
| `Finset.smulFinset` | $a \cdot t = \{a \cdot x : x \in t\}$ for $a \in \alpha$ |
| `Finset.vadd` | $s +_v t$, the additive version of `Finset.smul` |
| `Finset.vsub` | $s -_v t = \{x -_v y : x \in s, y \in t\}$, a finset of $\alpha$ |
| `Finset.sdiv` | $s /_s t$, the multiplicative version of `Finset.vsub` |

The translate `Finset.vaddFinset` is the additive version of `Finset.smulFinset`. Each operation is an image, as the definition lemmas `Finset.smul_def` and `Finset.smul_finset_def` show. So the target needs a decidable equality. The operations $-_v$ and $/_s$ go from two finsets of $\beta$ to a finset of $\alpha$, and so the decidable equality is on $\alpha$. They serve the torsors of Chapter 6, where the difference of two points is an element of the group.

#### The elementary lemmas

The lemmas follow the pattern of Section 3, with smul in the name for $s \cdot t$ and smul_finset for $a \cdot t$.

| Lean name | Statement |
| --- | --- |
| `Finset.mem_smul` | $x \in s \cdot t \iff \exists y \in s, \exists z \in t, y \cdot z = x$ |
| `Finset.mem_smul_finset` | $x \in a \cdot t \iff \exists y \in t, a \cdot y = x$ |
| `Finset.coe_smul` | $\uparrow(s \cdot t) = \uparrow s \cdot \uparrow t$ |
| `Finset.coe_smul_finset` | $\uparrow(a \cdot t) = a \cdot \uparrow t$ |
| `Finset.singleton_smul` | $\{a\} \cdot t = a \cdot t$ |
| `Finset.smul_finset_union` | $a \cdot (t_1 \cup t_2) = a \cdot t_1 \cup a \cdot t_2$ |
| `Finset.card_smul_le` | $\lvert s \cdot t \rvert \le \lvert s \rvert \, \lvert t \rvert$ |
| `Finset.card_smul_finset_le` | $\lvert a \cdot t \rvert \le \lvert t \rvert$ |

The coercion lemmas move each statement to the sets of Section 2. The lemmas `Set.toFinset_smul` and `Set.Finite.toFinset_smul` go the other way. The product is the union of the translates.

**Theorem.** $s \cdot t = \bigcup_{a \in s} a \cdot t$. This is `Finset.biUnion_smul_finset`.

*Proof.* An element of the left side is $a \cdot x$ with $a \in s$ and $x \in t$. This is the condition to be in $a \cdot t$ for some $a \in s$.

#### Actions on finsets

When a monoid $\alpha$ acts on $\beta$, it also acts on `Finset β` by translation. This is `Finset.mulActionFinset`, which gives $1 \cdot t = t$ and $(a b) \cdot t = a \cdot (b \cdot t)$. The finsets of $\alpha$ act on the finsets of $\beta$ by `Finset.mulAction`. The compatibility classes pass to finsets: `Finset.smulCommClass_finset` and `Finset.isScalarTower` and their variants make the translates commute when the original actions commute. So a lemma about actions in Chapter 6 applies to the action on finsets.

#### Cancellation and cardinality

The bound $|a \cdot t| \le |t|$ is an equality when the action of $a$ is injective. The class `IsLeftCancelSMul` says that $a \cdot x = a \cdot y$ gives $x = y$. Every group action has this property.

**Theorem.** If the scalar multiplication is left cancellative, then $|a \cdot t| = |t|$. This is `Finset.card_smul_finset`.

*Proof.* The finset $a \cdot t$ is the image of $t$ under $x \mapsto a \cdot x$. This map is injective, so `Finset.card_image_of_injective` gives the equality.

The same hypothesis makes the translation commute with the Boolean operations.

**Theorem.** If the scalar multiplication is left cancellative, then $a \cdot (s \cap t) = a \cdot s \cap a \cdot t$. This is `Finset.smul_finset_inter`.

*Proof.* The inclusion from left to right holds for every map. Conversely, let $a \cdot x = a \cdot y$ with $x \in s$ and $y \in t$. Cancellation gives $x = y$, so $x \in s \cap t$.

The lemmas `Finset.smul_finset_sdiff` and `Finset.smul_finset_symmDiff` give the difference and the symmetric difference. The lemma `Finset.smul_finset_subset_smul_finset_iff` states $a \cdot s \subseteq a \cdot t \iff s \subseteq t$. For an element $a$ that is only regular, the lemmas `IsSMulRegular.card_smul_finset` and `IsSMulRegular.smul_finset_inter` give the same results.

#### Group actions

For a group action, the inverse undoes the translation.

**Theorem.** $a^{-1} \cdot b \in t \iff b \in a \cdot t$. This is `Finset.inv_smul_mem_iff`.

*Proof.* If $b = a \cdot x$ with $x \in t$, then $a^{-1} \cdot b = x$. Conversely, $b = a \cdot (a^{-1} \cdot b)$.

The lemma `Finset.mem_inv_smul_finset_iff` is the form $b \in a^{-1} \cdot t \iff a \cdot b \in t$, and `Finset.smul_finset_subset_iff` states $a \cdot s \subseteq t \iff s \subseteq a^{-1} \cdot t$. In a finite type the whole finset is fixed by each translation, `Finset.smul_finset_univ`, and the converse holds: `Finset.smul_finset_eq_univ` states $a \cdot t = \mathrm{univ} \iff t = \mathrm{univ}$.

**Theorem.** If $s$ is a nonempty finset of the group, then $s \cdot \mathrm{univ} = \mathrm{univ}$. This is `Finset.smul_univ`.

*Proof.* Take $a \in s$. The translate $a \cdot \mathrm{univ}$ is $\mathrm{univ}$, and it is contained in $s \cdot \mathrm{univ}$.

The translates give a divisibility. Suppose that the translates $a \cdot t$ for $a \in s$ are pairwise disjoint or equal, in the sense that two different translates are disjoint. The finset $s \cdot t$ is their union, by `Finset.biUnion_smul_finset`, and each translate has $|t|$ elements, by `Finset.card_smul_finset`. So $|t|$ divides $|s \cdot t|$. This is `Finset.card_dvd_card_smul_right`. For a subgroup $H$ of a finite group $G$, seen as a finset, take $s = \mathrm{univ}$ and $t = H$ with the action of $G$ on itself by left multiplication. The translates $a \cdot H$ are the left cosets, so two of them are disjoint or equal. Since $\mathrm{univ} \cdot H = \mathrm{univ}$, the order $|H|$ divides $|G|$.

#### Products in a monoid

When $\alpha$ acts on itself, the translates connect with the products of Section 3. The lemma `Finset.singleton_mul` states $\{a\} s = a \cdot s$. The product on the other side uses the right action, which is the action of the opposite monoid $\alpha^{\mathrm{op}}$ of Chapter 1: `Finset.mul_singleton` states $s \{a\} = \operatorname{op}(a) \cdot s$. The proof of both lemmas is `Finset.mem_mul` and `Finset.mem_smul_finset` on the two sides. The product of two finsets is the union of right translates, by `Finset.biUnion_op_smul_finset`. In a semigroup, `Finset.op_smul_finset_mul_eq_mul_smul_finset` states $(s a) t = s (a t)$. In a group, `Finset.inv_smul_finset_distrib` states $(a s)^{-1} = s^{-1} a^{-1}$, written with the right action. Under left cancellation, `Finset.mul_mem_smul_finset_iff` states $a b \in a \cdot s \iff b \in s$.

The lemma `Finset.pairwiseDisjoint_smul_iff` states that the translates $a \cdot t$ for $a$ in a set $s$ are pairwise disjoint if and only if the map $(a, x) \mapsto a \cdot x$ is injective on $s \times t$. With `Finset.card_mul_iff` of Section 3, this characterizes the case $|s t| = |s| \, |t|$.

#### Common errors

1. The notation $a \cdot t$ for a finset and $s \cdot t$ for two finsets are different instances, `Finset.smulFinset` and `Finset.smul`. A rewrite with a lemma about one does not apply to the other. Use `Finset.singleton_smul` to pass from $\{a\} \cdot t$ to $a \cdot t$.
2. The right translate $t a$ is not `a • t`. In the library it is `MulOpposite.op a • t`, by `Finset.mul_singleton`. A learner who writes `a • t` for a right coset gets the left coset.
3. A learner forgets `open Pointwise` and gets an error that no scalar multiplication on `Finset β` exists. The instances are scoped, as in Section 3.

### Exercises

1. (A) In $\mathbb{Z}$, let $t = \{0, 1, 4\}$. Compute $3 +_v t$ and $\{0, 3\} +_v t$, and check the bound of `Finset.card_smul_le`.
2. (A) Show $a \cdot (s \setminus t) = a \cdot s \setminus a \cdot t$ for a group action with `Finset.smul_finset_sdiff`, and give a scalar multiplication on a finite type where the equality fails.
3. (B) Let $G$ act on a finite type $\beta$ and let $t$ be a finset of $\beta$. Show that $a \cdot t = t$ when $a \cdot t \subseteq t$. Hint: compare the cardinalities with `Finset.card_smul_finset`.
4. (B) Let $H$ be a finite subgroup of a group $G$ and $s$ a finset of $G$. Seen as a finset, $H$ gives the product $s H$. Show that $|H|$ divides $|s H|$ with `Finset.card_dvd_card_smul_right`.
5. (B) Show that $\{a\} s \{b\} = a \cdot (\operatorname{op}(b) \cdot s)$ in a monoid, with `Finset.singleton_mul` and `Finset.mul_singleton`.
6. (C) Let $G$ be a finite group and $t$ a nonempty finset of $G$. Show that the stabilizer $\{a : a \cdot t = t\}$ has order dividing $|t|$. Hint: $t$ is a union of right cosets of the stabilizer.

### Reference

<?reference?>
