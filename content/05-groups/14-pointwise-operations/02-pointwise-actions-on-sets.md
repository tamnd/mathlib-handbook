---
title: Pointwise actions on sets
kind: api
modules:
  - Mathlib.Algebra.Group.Pointwise.Set.Scalar
  - Mathlib.Algebra.Group.Pointwise.Set.Lattice
  - Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
  - Mathlib.Algebra.Group.Action.Pointwise.Set.Finite
explains:
  E2: [Set.mem_smul_set, Set.subset_smul_set_iff, Set.smul_set_compl, Set.smul_set_iInter, Set.pairwise_disjoint_smul_iff, Set.iUnion_smul_set, Set.mul_iUnion, Set.op_smul_set_mul_eq_mul_smul_set, Set.pair_mul, Set.finite_smul_set]
  E1: auto
families: []
requires: [V01, V05.C01, V05.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Pointwise actions on sets

### Overview

Let a type $\alpha$ act on a type $\beta$, with the action written $a \cdot x$. For $a \in \alpha$ and a subset $t$ of $\beta$, the *translate* $a \cdot t$ is the set of all $a \cdot y$ with $y \in t$. For a subset $s$ of $\alpha$, the set $s \cdot t$ is the set of all $x \cdot y$ with $x \in s$ and $y \in t$. When $\alpha = \beta$ is a group acting on itself by left multiplication, $a \cdot t$ is the left translate $a t$ and $s \cdot t$ is the pointwise product $s t$ of Section 1. Translates of sets appear in each part of group theory: the left cosets $a H$, the orbits of a set under an action, the tilings of a group by translates of one set, and the actions of a group on its subsets.

This section has three parts. The first part gives the operations $s \cdot t$, $a \cdot t$, and the operations $s -_v t$ and $s /_s t$ of torsors. The second part gives the behaviour of all the pointwise operations on unions and intersections. The third part gives the action of a monoid on the sets of $\beta$ and the facts that need a group: a translate by a group element is a bijection of the power set, so it respects complements, intersections and finiteness. The section uses the actions of Chapter 6.

### The library around it

#### The scope Pointwise

As in Section 1, all the instances of these modules are scoped. They become active only after `open Pointwise` (or `open scoped Pointwise`). Without that command, the expression a • s for a set $s$ does not elaborate. The action instance `Set.mulActionSet` is also a scoped instance, and it is not reducible: the library expects the scope to be open each time that the instance is used, and a reducible instance changes the behaviour of simp.

#### The operations

The module `Mathlib.Algebra.Group.Pointwise.Set.Scalar` defines four instances. `Set.smulSet` is the translate $a \cdot t$ by one element, and `Set.smul` is the product $s \cdot t$ of two sets. `Set.vsub` gives $s -_v t$, the set of the differences $x -_v y$ in a torsor (Chapter 6, Section 3), and `Set.sdiv` gives the scalar division $s /_s t$ of a multiplicative torsor. The additive forms `Set.vaddSet` and `Set.vadd` give the translates $a +_v t$ and $s +_v t$.

**Theorem (Membership).** $x \in a \cdot t$ if and only if $x = a \cdot y$ for some $y \in t$. Also $b \in s \cdot t$ if and only if $b = x \cdot y$ for some $x \in s$ and $y \in t$.

These are `Set.mem_smul_set` and `Set.mem_smul`, and they hold by the definitions as images. In the same way `Set.mem_vsub` and `Set.mem_sdiv` describe the torsor operations. The translate is an image: `Set.image_smul` states that the image of $t$ under $y \mapsto a \cdot y$ is $a \cdot t$. So all the lemmas about images apply to translates. The product of two sets is the union of the translates, by `Set.iUnion_smul_set` below, and `Set.singleton_smul` states $\{a\} \cdot t = a \cdot t$.

The rules for the empty set, singletons and unions follow the rules of Section 1. The lemmas `Set.smul_set_empty`, `Set.smul_set_singleton` and `Set.smul_set_union` give $a \cdot \emptyset = \emptyset$, $a \cdot \{b\} = \{a \cdot b\}$ and $a \cdot (t_1 \cup t_2) = a \cdot t_1 \cup a \cdot t_2$. A translate is monotone, by `Set.smul_set_mono`, and `Set.smul_set_subset_iff` states $a \cdot s \subseteq t$ if and only if $a \cdot b \in t$ for each $b \in s$. For intersections, only an inclusion holds in general: `Set.smul_set_inter_subset` gives $a \cdot (t_1 \cap t_2) \subseteq a \cdot t_1 \cap a \cdot t_2$.

#### Unions and intersections

The module `Mathlib.Algebra.Group.Pointwise.Set.Lattice` gives the behaviour of each pointwise operation on indexed unions and intersections. The rule is the same for each operation. A product of images is an image of a product, and images commute with unions. So each operation commutes with unions, and only an inclusion holds for intersections.

**Theorem.** For a set $s$ and a family $(t_i)$ of sets of a type with a product, $s \bigcup_i t_i = \bigcup_i s t_i$, but only $s \bigcap_i t_i \subseteq \bigcap_i s t_i$.

*Proof.* An element $x y$ with $x \in s$ and $y \in \bigcup_i t_i$ has $y \in t_i$ for some $i$, so $x y \in s t_i$. The converse inclusion follows from monotonicity. For the intersection, $s \bigcap_i t_i \subseteq s t_j$ for each $j$ by monotonicity. $\square$

These are `Set.mul_iUnion` and `Set.mul_iInter_subset`. The equality for intersections fails: in $\mathbb{Z}$, take $s = \{0, 1\}$, $t_1 = \{0\}$ and $t_2 = \{1\}$. Then $t_1 \cap t_2 = \emptyset$, but $s + t_1$ and $s + t_2$ both contain $1$. The names follow one pattern. The operation comes first, then the kind of union: `Set.iUnion_mul`, `Set.mul_iUnion₂` and `Set.mul_sUnion` are the forms for a family on the left, for a double family, and for a set of sets. The same names exist with div, smul, smul_set, vsub and sdiv in place of mul, for example `Set.smul_set_iUnion` and `Set.smul_set_iInter_subset`. The inverse commutes with both operations, by `Set.iUnion_inv` and `Set.iInter_inv`, because the inversion is a bijection.

A product of two sets is the union of the translates of one set.

**Theorem.** $s \cdot t = \bigcup_{a \in s} a \cdot t$.

*Proof.* Both sides consist of the elements $a \cdot y$ with $a \in s$ and $y \in t$. $\square$

This is `Set.iUnion_smul_set`, and `Set.iUnion_mul_left_image` is the form for a product of sets in a semigroup.

#### The action on sets

The module `Mathlib.Algebra.Group.Action.Pointwise.Set.Basic` makes the translates into an action. If a monoid $\alpha$ acts on $\beta$, then $\alpha$ acts on the sets of $\beta$ by `Set.mulActionSet`, and the monoid of sets `Set α` acts on `Set β` by `Set.mulAction`. The instances `Set.smulCommClass_set` and `Set.isScalarTower` move the commutation and the tower properties of Chapter 6 from $\beta$ to its sets. The lemma `Set.smul_set_prod` states $c \cdot (s \times t) = (c \cdot s) \times (c \cdot t)$, and `Set.smul_set_pi` gives the same for products of a family when the acting monoid is a group.

A group acts on the sets of $\beta$ by bijections. Most results of the module use this.

**Theorem.** Let a group $G$ act on $\beta$, and let $a \in G$. Then $x \in a \cdot t \iff a^{-1} \cdot x \in t$, and $s \subseteq a \cdot t \iff a^{-1} \cdot s \subseteq t$. The translate respects complements: $a \cdot t^{c} = (a \cdot t)^{c}$. It respects arbitrary intersections: $a \cdot \bigcap_i t_i = \bigcap_i a \cdot t_i$.

*Proof.* The map $y \mapsto a \cdot y$ is a bijection of $\beta$, with inverse $y \mapsto a^{-1} \cdot y$. So the translate $a \cdot t$ is the preimage of $t$ under $y \mapsto a^{-1} \cdot y$, which gives the first two statements. A preimage respects complements and intersections. $\square$

These are `Set.mem_smul_set_iff_inv_smul_mem`, `Set.subset_smul_set_iff`, `Set.smul_set_compl` and `Set.smul_set_iInter`. The preimage form is `Set.preimage_smul`: the preimage of $t$ under $y \mapsto a \cdot y$ is $a^{-1} \cdot t$. Injectivity is enough for intersections and differences: `Set.smul_set_inter` and `Set.smul_set_sdiff` ask only for the class `IsLeftCancelSMul`. The lemma `Set.disjoint_smul_set` states that $a \cdot s$ and $a \cdot t$ are disjoint if and only if $s$ and $t$ are disjoint. The lemmas `Set.smul_set_univ` and `Set.smul_univ` state that translates of the whole space are the whole space.

The next result is the basic tool for packings and tilings.

**Theorem.** Let $G$ act on $\beta$ and let $s \subseteq \beta$. The translates $a \cdot s$ for $a \in G$ are pairwise disjoint if and only if $a = 1$ for each $a$ with $a \cdot s \cap s \neq \emptyset$.

*Proof.* If $a \neq b$ and $a \cdot s$ meets $b \cdot s$, then $b^{-1} a \cdot s$ meets $s$ and $b^{-1} a \neq 1$. Conversely, if $a \neq 1$ and $a \cdot s$ meets $s = 1 \cdot s$, then two different translates meet. $\square$

This is `Set.pairwise_disjoint_smul_iff`. The variant `Set.pairwiseDisjoint_smul_iff` treats translates by the elements of one set $s$ of the acting type: they are pairwise disjoint if and only if the action map is injective on $s \times t$.

#### Products and translates in a group

When a semigroup acts on itself, the translates and the products of sets meet. The lemma `Set.pair_mul` states $\{a, b\} s = a s \cup b s$, and `Set.smul_set_subset_mul` gives $a t \subseteq s t$ for $a \in s$. Right translates use the opposite monoid of Chapter 1: the set $s a$ is $\operatorname{op}(a) \cdot s$. The lemma `Set.op_smul_set_mul_eq_mul_smul_set` states $(s a) t = s (a t)$, which is associativity. The lemma `Set.mul_pair` gives $s \{a, b\} = s a \cup s b$. For the inverse, `Set.inv_smul_set_distrib` states $(a s)^{-1} = s^{-1} a^{-1}$, in the form with $\operatorname{op}(a^{-1})$. The lemma `Set.smul_inter_nonempty_iff` states that $x s$ meets $t$ if and only if $x = a b^{-1}$ for some $a \in t$ and $b \in s$. The image under a homomorphism of a translate is a translate, by `Set.image_smul_distrib`.

In a commutative group, translates and quotients commute: `Set.smul_div_smul_comm` states $(a s) / (b t) = (a / b) (s / t)$. A homomorphism $f$ gives a graph, and `Set.smul_graphOn` computes the translate of the graph of $f$ on a set.

#### Finite and infinite translates

The module `Mathlib.Algebra.Group.Action.Pointwise.Set.Finite` gives finiteness. A translate of a finite set is finite for each action, by `Set.Finite.smul_set` of Section 1. For a group action the converse holds.

**Theorem.** Let a group act on $\beta$. Then $a \cdot s$ is finite if and only if $s$ is finite.

*Proof.* $a \cdot s$ is the image of $s$, and $s = a^{-1} \cdot (a \cdot s)$ is the image of $a \cdot s$. Images of finite sets are finite. $\square$

This is `Set.finite_smul_set`, and `Set.infinite_smul_set` is the form for infinite sets. The lemmas `Set.Finite.of_smul_set` and `Set.Infinite.smul_set` are the one-way forms. For the size, the module `Mathlib.Algebra.Group.Pointwise.Set.Card` of Section 1 gives `Set.natCard_smul_set`: a translate by a group element has the same size as the set.

#### Common errors

1. A learner writes `a • s` for an element $a$ and a set $s$, and Lean does not find the instance. The instance `Set.smulSet` is scoped. Add `open Pointwise`.
2. A learner uses `Set.smul_set_inter` for the action of a monoid that is not cancellative. The equality $a \cdot (s \cap t) = a \cdot s \cap a \cdot t$ needs `IsLeftCancelSMul`, for example a group action. For the action of $0$ on a ring, both $a \cdot s$ and $a \cdot t$ are $\{0\}$ for nonempty $s, t$, even when $s \cap t$ is empty. The general lemma is `Set.smul_set_inter_subset`.
3. A learner writes the right translate $s a$ as `s • a` or as `a • s`. In the library the right translate is `MulOpposite.op a • s`, or the product `s * {a}`. The lemma `Set.mul_singleton` converts the second form to an image.

### Exercises

1. (A) Let $G$ act on $\beta$ and let $a, b \in G$. Prove that $(a b) \cdot s = a \cdot (b \cdot s)$ for each set $s$, and find the general lemma of actions that gives this for the action `Set.mulActionSet`.
2. (A) In $\mathbb{Z}$, let $s = \{0, 1\}$, $t_1 = \{0, 2\}$ and $t_2 = \{1, 2\}$. Compute $s + (t_1 \cap t_2)$ and $(s + t_1) \cap (s + t_2)$, and check `Set.add_inter_subset` on this example.
3. (B) Let $H$ be a subgroup of $G$. Prove that two left cosets $a H$ and $b H$ are equal or disjoint, using `Set.disjoint_smul_set_left`.
4. (B) Let $G$ be a group and let $s \subseteq G$ be finite and nonempty. Prove that the translates $a s$ for $a \in G$ are pairwise disjoint if and only if $s$ has exactly one element. Use `Set.pairwise_disjoint_smul_iff`.
5. (B) Let $G$ act on $\beta$ and let $s \subseteq \beta$. Prove that the set $\{a \in G : a \cdot s = s\}$ is a subgroup of $G$. Use `Set.subset_smul_set_iff` to treat the inverse.
6. (C) Let $G$ be an infinite group and $s \subseteq G$ finite. Prove that there is an $a \in G$ with $a s \cap s = \emptyset$. Hint: the set of $a$ with $a s \cap s \neq \emptyset$ is $s s^{-1}$, by `Set.smul_inter_nonempty_iff`, and it is finite.

### Reference

<?reference?>
