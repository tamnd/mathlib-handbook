---
title: Intervals and bounds under the group operations
kind: api
modules:
  - Mathlib.Algebra.Order.Group.Pointwise.Bounds
  - Mathlib.Algebra.Order.Group.Pointwise.Interval
  - Mathlib.Algebra.Order.Interval.Set.Group
  - Mathlib.Algebra.Order.Interval.Set.Monoid
  - Mathlib.Algebra.Order.Interval.Finset.Basic
  - Mathlib.Algebra.Order.Interval.Multiset
  - Mathlib.Algebra.Order.UpperLower
  - Mathlib.Algebra.Order.Group.Action
  - Mathlib.Algebra.Order.Group.Action.Flag
  - Mathlib.Algebra.Order.Group.Action.Synonym
explains:
  E2: [IsLUB.add, isLUB_neg, BddAbove.add, Set.Icc_add_Icc, Set.neg_Icc, Set.image_const_sub_Icc, Set.Icc_add_bij, Set.mem_Icc_iff_abs_le, IsUpperSet.add_left, smul_mono_right]
  E1: auto
families: []
requires: [V04.C01, V04.C04, V04.C07, V04.C08, V01.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Intervals and bounds under the group operations

### Overview

Chapter 7 defines the intervals of an order, and Chapter 1 defines the upper and lower bounds of a set. In an ordered group these sets move in a regular way under the operations. A translate of $[a, b]$ by $c$ is $[a + c, b + c]$, the negative of $[a, b]$ is $[-b, -a]$, and the sum of two intervals is an interval. The least upper bound of a pointwise sum $s + t$ is the sum of the least upper bounds. This section describes the files that state these rules.

The rules are short, but a proof in analysis uses them all the time. A bound such as $|x - y| \le \varepsilon$ is a statement about an interval, and the image of an interval under $x \mapsto 2x + 1$ is an interval with known ends. The section also treats upper sets under the pointwise product, and actions of a monoid on an order that keep the order.

### The library around it

#### Bounds of pointwise sums and negatives

For sets $s$ and $t$ of a type with an addition, $s + t$ is the set of the sums $x + y$ with $x \in s$ and $y \in t$, and $-s$ is the set of the negatives. These are the pointwise operations of the algebra volumes. The file `Mathlib.Algebra.Order.Group.Pointwise.Bounds` gives their bounds.

The lemma `BddAbove.add` states that $s + t$ is bounded above when $s$ and $t$ are, if addition is monotone on both sides. The proof is direct: if $x \le a$ on $s$ and $y \le b$ on $t$, then $x + y \le a + b$. The lemma `subset_upperBounds_mul` is the multiplicative form of the same fact for the sets of bounds.

In a group the statement is exact. The lemma `IsLUB.add` states that if $a$ is the least upper bound of $s$ and $b$ of $t$, then $a + b$ is the least upper bound of $s + t$. That $a + b$ is an upper bound is the previous paragraph. For the other half, let $c$ be an upper bound of $s + t$ and fix $y \in t$. Then $x \le c - y$ for each $x \in s$, so $a \le c - y$, and $y \le c - a$. This holds for each $y \in t$, so $b \le c - a$ and $a + b \le c$. The proof uses the negatives, and the lemma needs `AddGroup`. The forms `IsGLB.add`, `IsLUB.sub` and `IsLUB.mul` treat the other cases.

The negation reverses the order, so it exchanges upper and lower bounds. The lemma `isLUB_neg` states that $a$ is the least upper bound of $-s$ if and only if $-a$ is the greatest lower bound of $s$. The lemma `IsLUB.neg` is one direction, and `bddAbove_inv` and `BddAbove.neg` are the forms for bounded sets. With these lemmas, a result about infima often follows from the result about suprema applied to $-s$.

#### Intervals under the operations

The file `Mathlib.Algebra.Order.Group.Pointwise.Interval` computes the images of intervals. In an ordered additive commutative group, `Set.neg_Icc` states $-[a, b] = [-b, -a]$, and `Set.neg_Ioi` and the other forms treat each kind of interval. The lemma `Set.image_const_sub_Icc` states that $x \mapsto a - x$ sends $[b, c]$ to $[a - c, a - b]$. The lemmas with the pattern `Set.image_add_const_Icc` and `Set.image_div_const_Icc` treat translations and the multiplicative forms. In a division semiring, `Set.image_affine_Icc'` states that for $a > 0$ the map $x \mapsto a x + b$ sends $[c, d]$ to $[a c + b, a d + b]$. For a group with zero, `Set.inv_Ioo_0_left` states that the inverse of $(0, a)$ is $(a^{-1}, \infty)$ when $a > 0$.

The sum of two intervals is in the interval of the sums, by `Set.Icc_add_Icc_subset`, when addition is monotone. In a linear order, `Set.Icc_add_Icc` states the equation $[a, b] + [c, d] = [a + c, b + d]$ for $a \le b$ and $c \le d$. The proof of the reverse inclusion is a case split for groups. Let $z$ be in $[a + c, b + d]$. If $z \le b + c$, then $z = (z - c) + c$ with $z - c$ in $[a, b]$. Otherwise $b + c < z$, and $z = b + (z - b)$ with $z - b$ in $(c, d]$. The lemma for monoids replaces the subtraction by `ExistsAddOfLE`. The lemma `Set.Icc_sub_Icc` states $[a, b] - [c, d] = [a - d, b - c]$. For a canonically ordered monoid, `Set.Ici_add_Ici_eq` states $[a, \infty) + [b, \infty) = [a + b, \infty)$, and `Set.Ici_nsmul_eq` gives the multiples.

The same file has lemmas about the interval between two points in either order, `Set.uIcc` of Chapter 7. The lemma `Set.abs_sub_le_of_uIcc_subset_uIcc` states that $|d - c| \le |b - a|$ when the interval of $c$ and $d$ lies in the interval of $a$ and $b$.

#### Membership in a translated interval

The file `Mathlib.Algebra.Order.Interval.Set.Group` moves a membership across a sum. The lemma `Set.sub_mem_Icc_iff_left` states $a - b \in [c, d] \leftrightarrow a \in [c + b, d + b]$, and `Set.neg_mem_Icc_iff` and `Set.inv_mem_Icc_iff` treat negatives and inverses. The lemma `Set.mem_Icc_iff_abs_le` states
$$|x - y| \le z \leftrightarrow y \in [x - z, x + z].$$
This is the usual form of a neighbourhood of $x$ in an ordered group. The lemma `Set.pairwise_disjoint_Ico_zsmul` states that the intervals $[n b, (n + 1) b)$ for $n \in \mathbb{Z}$ are pairwise disjoint. With an archimedean order these intervals cover the group, and so each element lies in exactly one of them. The lemma `Set.nonempty_Ico_sdiff` states that $[x, x + d_1)$ is not contained in $[y, y + d_2)$ when $d_2 < d_1$ and $0 < d_1$.

The file `Mathlib.Algebra.Order.Interval.Set.Monoid` gives the translations without negatives, for an ordered cancellative monoid with `ExistsAddOfLE` such as $\mathbb{N}$. The lemma `Set.Icc_add_bij` states that $x \mapsto x + d$ is a bijection from $[a, b]$ onto $[a + d, b + d]$. The lemmas such as `Set.image_add_const_Icc` give the image alone.

#### Finite intervals under translation

For a locally finite order, Chapter 7 defines the finite intervals `Finset.Icc a b`. The file `Mathlib.Algebra.Order.Interval.Finset.Basic` gives their translates. The lemma `Finset.map_add_left_Icc` states that the image of `Finset.Icc a b` under the embedding $x \mapsto c + x$ is `Finset.Icc (c + a) (c + b)`, and `Finset.image_add_left_Icc` is the form with an image. These lemmas let a sum over $[a, b]$ in $\mathbb{N}$ be moved to a sum over $[0, b - a]$. The file `Mathlib.Algebra.Order.Interval.Multiset` gives the same lemmas for `Multiset.Icc`, such as `Multiset.map_add_left_Icc`.

#### Upper sets in an ordered group

In an ordered commutative group, a product of sets is an upper set as soon as one factor is. The lemma `IsUpperSet.add_left` in `Mathlib.Algebra.Order.UpperLower` states that $s + t$ is an upper set when $t$ is. For the proof, let $x + y \le z$ with $x \in s$ and $y \in t$. Then $y \le z - x$, so $z - x$ is in $t$, and $z = x + (z - x)$ is in $s + t$. The lemma `IsLowerSet.inv` states that the inverse of a lower set is an upper set.

So the bundled upper sets of Chapter 4 form a commutative monoid, with the instance `UpperSet.instCommMonoid`. The product is the pointwise product, as `UpperSet.coe_mul` states, and the unit is $[1, \infty)$, as `UpperSet.coe_one` states. The closure commutes with the product: `upperClosure_add_distrib` states that the upper closure of $s + t$ is the sum of the closures.

#### Actions that keep the order

A monoid $M$ acts on an order $\alpha$ monotonically if $a \le b$ gives $m \cdot a \le m \cdot b$. The file `Mathlib.Algebra.Order.Group.Action` states this with a covariant class of Chapter 8. The lemma `smul_mono_right` states that $a \mapsto m \cdot a$ is monotone, and `smul_le_smul_left` is the form with two elements. In a semilattice, `smul_inf_le` gives $m \cdot (a \sqcap b) \le m \cdot a \sqcap m \cdot b$. The lemma `le_pow_smul` states that $a \le m \cdot a$ gives $a \le m^n \cdot a$ for each $n$, by induction. For a group action, `smul_top` states $g \cdot \top = \top$. The reason is that $g^{-1} \cdot \top \le \top$, and the action of $g$ gives $\top \le g \cdot \top$.

The file `Mathlib.Algebra.Order.Group.Action.Flag` lets the order automorphisms of $\alpha$ act on the flags of $\alpha$, the maximal chains of Chapter 1, by the instance `Flag.instMulActionOrderIso`. The image of a maximal chain under an order automorphism is again a maximal chain. The file `Mathlib.Algebra.Order.Group.Action.Synonym` carries actions to the type synonyms: `OrderDual.instMulAction` lets the order dual of $M$ act on $\alpha$ as $M$ does, and `Lex.instMulAction` does the same for `Lex M`.

#### Common errors

1. The lemma `Set.Icc_add_Icc` needs a linear order and the hypotheses $a \le b$ and $c \le d$. In a partial order, use the inclusion `Set.Icc_add_Icc_subset`. If $b < a$, the left side is empty and the right side need not be.
2. The lemma `IsLUB.add` does not hold in an ordered monoid without negatives. Its proof divides by the elements of the set. For $[0, \infty]$ or $\mathbb{N}$, prove the bound directly, or use the lemmas of Chapter 5 about suprema of sums.
3. The lemma `Set.mem_Icc_iff_abs_le` has the center $x$ on the left side and the point $y$ on the right side. A rewrite in the wrong direction gives an interval around the wrong point. Use `abs_sub_comm` first when the difference is $|y - x|$.

### Exercises

1. (A) Prove `Set.neg_Icc` in an ordered additive group from the membership lemma of $[a, b]$ and `neg_le_neg_iff`.
2. (A) Use `Set.image_affine_Icc'` to compute the image of $[0, 1]$ under $x \mapsto 3x - 2$ on $\mathbb{R}$.
3. (B) Prove `Set.Icc_add_Icc` for $\mathbb{Z}$ with the case split of this section, and show that it fails for $a = 1$, $b = 0$, $c = 0$ and $d = 5$.
4. (B) Prove `isLUB_neg` without the lemma itself, and deduce `IsGLB.add` from `IsLUB.add`.
5. (B) Prove `IsUpperSet.add_left`, and show that the sum of two lower sets need not be an upper set.
6. (C) In an archimedean ordered additive group with $b > 0$, show that each element lies in exactly one interval $[n b, (n + 1) b)$, with `Set.pairwise_disjoint_Ico_zsmul` for the uniqueness.

### Reference

<?reference?>
