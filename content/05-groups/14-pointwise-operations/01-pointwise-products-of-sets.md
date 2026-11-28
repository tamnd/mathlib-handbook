---
title: Pointwise products of sets
kind: api
modules:
  - Mathlib.Algebra.Group.Pointwise.Set.Basic
  - Mathlib.Algebra.Group.Pointwise.Set.BigOperators
  - Mathlib.Algebra.Group.Pointwise.Set.ListOfFn
  - Mathlib.Algebra.Group.Pointwise.Set.SelfInv
  - Mathlib.Algebra.Group.Pointwise.Set.Small
  - Mathlib.Algebra.Group.Pointwise.Set.Card
  - Mathlib.Algebra.Group.Pointwise.Set.Finite
  - Mathlib.Algebra.Group.TypeTags.Pointwise
explains:
  E2: [Set.mem_mul, Set.mul_subset_mul, Set.singletonMonoidHom, Set.isUnit_iff, Set.one_mem_div_iff, Set.mem_pow_iff_prod, Set.Finite.mul, Set.natCard_mul_le, Set.isSelfInv_union_inv]
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

## Pointwise products of sets

### Overview

Let $\alpha$ have a product. For subsets $s$ and $t$ of $\alpha$, the *pointwise product* $s t$ is the set of all $x y$ with $x \in s$ and $y \in t$. The *pointwise inverse* $s^{-1}$ is the set of all $x^{-1}$ with $x \in s$, and the set $1$ is the singleton $\{1\}$. With these operations, the power set of a monoid is a monoid, and the power set of a commutative monoid is a commutative monoid. Products of sets appear in many places: the product $H K$ of two subgroups, the sets $s^n$ of words of length $n$ in a generating set, the difference sets $s / s$ of additive combinatorics, and the neighbourhoods $U U^{-1}$ of topological groups.

This section gives the algebra of these sets. It treats the definitions and the membership lemmas, the monotonicity of the operations, the monoid of sets and its units, the products over lists and finite sets, and the size of a product. The action of an element on a set, as in a translate $a s$, is the subject of Section 2. The same theory for finite sets, with the type `Finset`, is the subject of Sections 3 and 4.

### The library around it

#### The scope Pointwise

The instances of this section are *scoped*: they are active only after the command `open Pointwise`. The reason is a conflict of notation. For $n : \mathbb{N}$ and a set $s$ of an additive monoid, $n \cdot s$ can be the pointwise scalar multiple $\{n x : x \in s\}$ or the $n$-fold sum $s + \dots + s$. These two sets are different in general: for $s = \{0, 1\}$ in $\mathbb{Z}$, the first is $\{0, 2\}$ and the second is $\{0, 1, 2\}$. The library takes the second meaning, the power in the monoid of sets, and the library note `LibraryNote.pointwise_nat_action` explains the choice. Because the choice is not the only possible one, the instances do not apply by default. In a file that uses $s t$, $s^{-1}$ or $s^n$ for sets, write `open Pointwise` first, or `open scoped Pointwise`.

#### The operations and membership

The module `Mathlib.Algebra.Group.Pointwise.Set.Basic` defines the instances `Set.one`, `Set.mul`, `Set.inv` and `Set.div`, and the powers `Set.NPow` and `Set.ZPow`. The additive forms `Set.zero`, `Set.add`, `Set.neg`, `Set.sub` and `Set.NSMul` come from the same source by the additive translation. The product is the image of the product map: `Set.image2_mul` states $\operatorname{image2}(\cdot)\, s\, t = s t$. So the general lemmas about `Set.image2` apply to products. The inverse is a preimage: `Set.inv_preimage` states that $s^{-1}$ is the preimage of $s$ under the inversion.

**Theorem (Membership).** Let $a \in \alpha$. Then $a \in s t$ if and only if $a = x y$ for some $x \in s$ and $y \in t$, and $a \in s^{-1}$ if and only if $a^{-1} \in s$.

These are `Set.mem_mul` and `Set.mem_inv`. The first is true by the definition of the image, and the second is true by the definition of the preimage. The introduction rules are `Set.mul_mem_mul`, `Set.div_mem_div` and `Set.pow_mem_pow`. The lemma `Set.inv_mem_inv` states $a^{-1} \in s^{-1} \iff a \in s$ when the inversion is involutive. For the inverse, `Set.mem_inv` is the simp normal form, so simp rewrites a goal $a \in s^{-1}$ to $a^{-1} \in s$.

The singletons compute as the products of elements: `Set.singleton_mul_singleton` states $\{a\}\{b\} = \{a b\}$, and `Set.singleton_mul` and `Set.mul_singleton` give $\{a\} t$ and $s \{b\}$ as images of translations. The empty set absorbs: `Set.empty_mul` and `Set.mul_empty`, and `Set.mul_eq_empty` states $s t = \emptyset \iff s = \emptyset \lor t = \emptyset$. The product distributes over unions, by `Set.union_mul` and `Set.mul_union`, but not over intersections: `Set.inter_mul_subset` gives only $(s_1 \cap s_2) t \subseteq s_1 t \cap s_2 t$. The inverse commutes with all the set operations, by `Set.union_inv`, `Set.inter_inv` and `Set.compl_inv`.

#### Monotonicity

**Theorem (Monotonicity).** If $s_1 \subseteq t_1$ and $s_2 \subseteq t_2$, then $s_1 s_2 \subseteq t_1 t_2$.

*Proof.* Let $x y \in s_1 s_2$ with $x \in s_1$ and $y \in s_2$. Then $x \in t_1$ and $y \in t_2$, so $x y \in t_1 t_2$. $\square$

This is `Set.mul_subset_mul`, with the one-sided forms `Set.mul_subset_mul_left` and `Set.mul_subset_mul_right`. The instances `Set.instMulLeftMono` and `Set.instMulRightMono` record the same fact for the order on sets, so the general lemmas of ordered monoids apply. The criterion for a product to lie in a set is `Set.mul_subset_iff`: $s t \subseteq u$ if and only if $x y \in u$ for all $x \in s$ and $y \in t$. For powers, `Set.pow_subset_pow_left` states that $s \subseteq t$ implies $s^n \subseteq t^n$. If $1 \in s$, then the powers increase: `Set.pow_subset_pow_right` gives $s^m \subseteq s^n$ for $m \le n$, and `Set.subset_mul_left` gives $s \subseteq s t$ when $1 \in t$.

#### The monoid of sets and its units

When $\alpha$ is a monoid, the definitions `Set.semigroup`, `Set.monoid` and `Set.commMonoid` give the structures on `Set α`. When $\alpha$ is a division monoid, `Set.divisionMonoid` gives a division monoid. A set of a group is not a group in general, because $s s^{-1}$ is not $\{1\}$ when $s$ has two elements. The map $a \mapsto \{a\}$ is a homomorphism of monoids, `Set.singletonMonoidHom`, since $\{a\}\{b\} = \{a b\}$ and $\{1\} = 1$ (the lemma `Set.singleton_one`). The lemma `Set.singleton_pow` gives $\{a\}^n = \{a^n\}$.

**Theorem (Units of the monoid of sets).** Let $\alpha$ be a division monoid. A set $s$ is a unit of `Set α` if and only if $s = \{a\}$ for a unit $a$ of $\alpha$.

*Proof.* A singleton of a unit is a unit, since $\{a\}\{a^{-1}\} = \{1\}$. Conversely, let $s t = 1$. Then $s$ and $t$ are not empty. For $x, x' \in s$ and $y \in t$, both $x y$ and $x' y$ are $1$, so $x = x' = y^{-1}$. So $s = \{a\}$ and $t = \{b\}$ with $a b = 1$. $\square$

This is `Set.isUnit_iff`, and `Set.mul_eq_one_iff` is the main step. In a group the condition on $a$ is automatic, and `Set.isUnit_iff_singleton` states that the units are exactly the singletons.

#### Division and disjointness

In a group, the set $s / t = \{x y^{-1}\}$ detects intersections.

**Theorem.** In a group, $1 \in s / t$ if and only if $s$ and $t$ meet.

*Proof.* If $x \in s \cap t$, then $1 = x / x \in s / t$. Conversely, if $1 = x / y$ with $x \in s$ and $y \in t$, then $x = y$ is in $s \cap t$. $\square$

This is `Set.one_mem_div_iff`, in the form $1 \in s / t \iff \lnot \operatorname{Disjoint}(s, t)$. The lemmas `Set.one_notMem_div_iff` and `Set.one_mem_inv_mul_iff` are the negated form and the form with $t^{-1} s$. In particular `Set.Nonempty.one_mem_div` gives $1 \in s / s$ for each nonempty $s$. The lemma `Set.univ_mul` states that the product of the whole group with a nonempty set is the whole group.

#### Images and products

A multiplicative map respects the products: `Set.image_mul` states $f(s t) = f(s) f(t)$ for each `MulHomClass` map $f$. The lemmas `Set.image_inv`, `Set.image_div` and `Set.image_pow` do the same for the inverse, division and powers of a monoid homomorphism. The preimage needs more: `Set.preimage_mul` asks that $f$ is injective and that $s$ and $t$ lie in its range. The opposite monoid reverses products: `Set.image_op_mul` states $\operatorname{op}(s t) = \operatorname{op}(t) \operatorname{op}(s)$. For products of types, `Set.prod_mul_prod_comm` states $(s_1 \times t_1)(s_2 \times t_2) = (s_1 s_2) \times (t_1 t_2)$.

The module `Mathlib.Algebra.Group.TypeTags.Pointwise` treats the type tags of Section 9 of Chapter 1. The map `Multiplicative.ofAdd` sends sums of sets to products: `Multiplicative.ofAdd_image_setAdd` states that the image of $s + t$ is the product of the images, and `Multiplicative.ofAdd_image_nsmul` sends $n \cdot s$ to the power $n$. The lemmas `Multiplicative.toAdd_image_setMul` and `Multiplicative.toAdd_image_nsmul` go in the other direction.

#### Products over lists and finite sets

The module `Mathlib.Algebra.Group.Pointwise.Set.BigOperators` describes the products $\prod_{i \in I} s_i$ of finitely many sets in the monoid of sets.

**Theorem.** In a commutative monoid, $a \in s^n$ if and only if $a = \prod_{i < n} f(i)$ for some $f : \operatorname{Fin} n \to \alpha$ with $f(i) \in s$ for each $i$.

*Proof.* Induct on $n$. For $n = 0$ both sides say $a = 1$. The step uses $s^{n+1} = s^n s$ and `Fin.prod_univ_castSucc`, which splits the product over $\operatorname{Fin}(n+1)$ into the product over $\operatorname{Fin} n$ and the last factor. $\square$

This is `Set.mem_pow_iff_prod`, and `Set.mem_nsmul_iff_sum` is the additive form. The general forms are `Set.mem_finsetProd` and `Set.mem_fintype_prod`. The lemmas `Set.finsetProd_mem_finsetProd` and `Set.list_prod_mem_list_prod` are the introduction rules, and `Set.finsetProd_singleton` and `Set.list_prod_singleton` compute the product of singletons. The images under a homomorphism follow from `Set.image_list_prod` and `Set.image_finsetProd`.

The module `Mathlib.Algebra.Group.Pointwise.Set.ListOfFn` treats the case of a monoid that is not commutative. There the order of the factors matters, and the products are products of lists. The lemma `Set.mem_pow` states that $a \in s^n$ if and only if $a$ is the product of the list List.ofFn of some $f : \operatorname{Fin} n \to s$. The lemmas `Set.mem_prod_list_ofFn` and `Set.mem_list_prod` describe the product of a list of different sets.

#### Self-inverse sets

A set $s$ is *self-inverse*, or *symmetric*, if $s^{-1} = s$. The predicate is `IsSelfInv s`, the predicate of Section 7 of Chapter 1 applied in the monoid of sets. The module `Mathlib.Algebra.Group.Pointwise.Set.SelfInv` gives its closure properties. Self-inverse sets are closed under unions, intersections and complements, by `Set.IsSelfInv.union`, `Set.IsSelfInv.inter` and `Set.IsSelfInv.compl`, and under arbitrary unions and intersections, by `Set.IsSelfInv.iUnion` and `Set.IsSelfInv.iInter`. The criterion `Set.isSelfInv_iff_forall_inv_mem` states that, for an involutive inverse, $s$ is self-inverse if and only if $x^{-1} \in s$ for each $x \in s$.

**Theorem.** For each set $s$ with an involutive inverse, $s \cup s^{-1}$ and $s \cap s^{-1}$ are self-inverse.

*Proof.* $(s \cup s^{-1})^{-1} = s^{-1} \cup (s^{-1})^{-1} = s^{-1} \cup s$, and the same computation works for the intersection. $\square$

These are `Set.isSelfInv_union_inv` and `Set.isSelfInv_inter_inv`. A generating set of a group is often replaced by $s \cup s^{-1}$, and then the closure of $s$ is the union of the powers of $s \cup s^{-1} \cup \{1\}$.

#### Size: finite, small and cardinal

The module `Mathlib.Algebra.Group.Pointwise.Set.Finite` gives finiteness. The product of two finite sets is finite, by `Set.Finite.mul`, because it is the image of the finite set $s \times t$. The lemmas `Set.Finite.inv` and `Set.Finite.div` treat the inverse and the quotient. With cancellation the converse holds for nonempty sets: `Set.finite_mul` states that $s t$ is finite if and only if $s$ and $t$ are finite, or one of them is empty. The instance `Set.fintypeMul` gives a `Fintype` structure on $s t$ from structures on $s$ and $t$. In a finite group, the powers of a set stop growing: `Group.card_pow_eq_card_pow_card_univ` states that $|S^k| = |S^{|G|}|$ for $k \ge |G|$.

The module `Mathlib.Algebra.Group.Pointwise.Set.Card` bounds the size. The lemma `Cardinal.mk_mul_le` gives $\# (s t) \le \# s \cdot \# t$ for cardinals. For the natural number cardinality, `Set.natCard_mul_le` gives $|s t| \le |s| \cdot |t|$, but it needs a cancellative product. The reason is the convention that `Nat.card` of an infinite set is $0$. In a monoid with a zero, take $s$ infinite and $t = \{0\}$: then $s t = \{0\}$ has one element, but $|s| \cdot |t| = 0$. The inverse keeps the size: `Set.natCard_inv`, `Set.ncard_inv` and `Set.encard_inv`.

The module `Mathlib.Algebra.Group.Pointwise.Set.Small` gives the instances `small_mul`, `small_div` and `small_set_one`. They state that the product of two small sets is small, in the sense of the class `Small` of Volume 1. They let a proof move a product of sets to a type in a lower universe.

#### Common errors

1. A learner writes `s * t` for two sets and Lean reports that it cannot find the instance `HMul (Set α) (Set α) ?_`. The instances are scoped. Add `open Pointwise` at the top of the file or the section.
2. A learner reads $2 \cdot s$ for a set $s$ of an additive group as $\{2 x : x \in s\}$. In the library it is $s + s$, the power in the monoid of sets. The set $\{2 x : x \in s\}$ is the image of $s$ under the map $x \mapsto 2 x$, and it is a subset of $s + s$.
3. A learner expects $s s^{-1} = 1$ for a set $s$ of a group. This is true only for singletons, by `Set.isUnit_iff_singleton`. In general $s s^{-1}$ contains $1$ when $s$ is not empty, and it is larger than $\{1\}$ when $s$ has two elements.

### Exercises

1. (A) Let $s = \{0, 1\}$ in $\mathbb{Z}$. Compute $s + s$, $3 \cdot s$ in the pointwise sense of the library, and the image of $s$ under $x \mapsto 3 x$. Then prove in Lean that $2 \in 3 \cdot s$, with `Set.mem_nsmul_iff_sum` or with `Set.mem_add`.
2. (A) Prove that $(s t)^{-1} = t^{-1} s^{-1}$ for sets of a group. Prove it first by hand from `Set.mem_mul` and `Set.mem_inv`, and then find the general lemma of division monoids that gives it in the monoid of sets.
3. (B) Let $H$ and $K$ be subgroups of a group $G$, viewed as sets. Prove that $H K$ is a subgroup if and only if $H K = K H$. Use `Set.mul_subset_iff` for one inclusion.
4. (B) Let $G$ be a group and let $s$ be a subset with $1 \in s$ and $s^{-1} = s$. Prove that $\bigcup_n s^n$ is the subgroup generated by $s$. Use `Set.pow_subset_pow_right` to see that the union is directed.
5. (A) Let $s$ and $t$ be finite subsets of a group, with $t$ not empty. Prove that $|s t| \ge |s|$. Hint: for $b \in t$, the set $s \{b\}$ is a subset of $s t$, and `Set.mul_singleton` describes it as an image under an injective map.
6. (C) Let $G$ be a finite group and $s, t$ subsets with $|s| + |t| > |G|$. Prove that $s t = G$. Hint: for $g \in G$, the sets $s$ and $g t^{-1}$ meet, and `Set.one_mem_div_iff` turns this into $g \in s t$.

### Reference

<?reference?>
