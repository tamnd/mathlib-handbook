---
title: Two-sided ideals and simple rings
kind: api
modules:
  - Mathlib.RingTheory.TwoSidedIdeal.Basic
  - Mathlib.RingTheory.TwoSidedIdeal.BigOperators
  - Mathlib.RingTheory.TwoSidedIdeal.Instances
  - Mathlib.RingTheory.TwoSidedIdeal.Kernel
  - Mathlib.RingTheory.TwoSidedIdeal.Lattice
  - Mathlib.RingTheory.TwoSidedIdeal.Operations
  - Mathlib.RingTheory.SimpleRing.Basic
  - Mathlib.RingTheory.SimpleRing.Congr
  - Mathlib.RingTheory.SimpleRing.Defs
  - Mathlib.RingTheory.SimpleRing.DivisionRing
  - Mathlib.RingTheory.SimpleRing.Field
  - Mathlib.RingTheory.SimpleRing.Matrix
  - Mathlib.RingTheory.SimpleRing.Principal
explains:
  E2: [TwoSidedIdeal.rel_iff, TwoSidedIdeal.ker_eq_bot, TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure, IsSimpleRing.one_mem_of_ne_zero_mem, RingHom.injective, isSimpleRing_iff_isField, IsSimpleRing.isField_center]
  E1: auto
families: []
requires: [V06.C01, V06.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Two-sided ideals and simple rings

### Overview

The ideals of the earlier sections live in a commutative ring. In a noncommutative ring there are three kinds of ideals: left ideals, right ideals and two-sided ideals. The type `Ideal R` of Mathlib is the type of left ideals, since it is defined as `Submodule R R`. The quotient ring $R/I$ exists only when $I$ is two-sided. So the library has a second type, `TwoSidedIdeal R`, for the ideals that are kernels of ring homomorphisms.

This section explains that type, its lattice, its spans and kernels, and its relation to `Ideal R`. It then treats simple rings: the nonzero rings with no two-sided ideals other than $0$ and the whole ring. A commutative ring is simple exactly when it is a field, so the notion is new only in the noncommutative case. Matrix rings over a division ring are the main examples, and Section 4 of Chapter 4 uses them in the theorem of Wedderburn and Artin.

### The library around it

#### Two-sided ideals as congruences

**Definition (Two-sided ideal).** Let $R$ be a ring. A two-sided ideal of $R$ is an additive subgroup $I$ with $r x \in I$ and $x r \in I$ for all $r \in R$ and $x \in I$.

The module `Mathlib.RingTheory.TwoSidedIdeal.Basic` does not define a two-sided ideal as a set. It defines the structure `TwoSidedIdeal R` with one field `ringCon : RingCon R`, a congruence relation for both the addition and the multiplication. The ideal is the class of $0$: `TwoSidedIdeal.mem_iff` states $x \in I \iff x \sim_I 0$. The ring needs only `[NonUnitalNonAssocRing R]`, so the definition covers rings without a unit and without associativity.

**Theorem (Congruences and ideals).** For a two-sided ideal $I$ and $x, y \in R$, $x \sim_I y$ if and only if $x - y \in I$.

*Proof.* If $x \sim_I y$, then $x - y \sim_I y - y = 0$, since a congruence for addition is compatible with adding $-y$. So $x - y \in I$. Conversely, if $x - y \sim_I 0$, add $y$ to both sides: $x \sim_I y$. $\square$

This is `TwoSidedIdeal.rel_iff`. The order isomorphism `TwoSidedIdeal.orderIsoRingCon` identifies the two-sided ideals with the ring congruences, and `TwoSidedIdeal.ringCon_injective` and `TwoSidedIdeal.ringCon_le_iff` are its parts. A user who has a set and the closure properties uses the constructor `TwoSidedIdeal.mk'`. It takes the carrier and the proofs that the carrier contains $0$ and is closed under addition, negation and multiplication on both sides, and `TwoSidedIdeal.mem_mk'` computes membership. For a given ideal these five properties are the lemmas `TwoSidedIdeal.zero_mem`, `TwoSidedIdeal.add_mem`, `TwoSidedIdeal.neg_mem`, `TwoSidedIdeal.mul_mem_left` and `TwoSidedIdeal.mul_mem_right`, and `TwoSidedIdeal.sub_mem`, `TwoSidedIdeal.nsmul_mem` and `TwoSidedIdeal.zsmul_mem` follow. Two ideals with the same elements are equal by `TwoSidedIdeal.ext`.

The instance `TwoSidedIdeal.setLike` makes an ideal a set, and `TwoSidedIdeal.instAddSubgroupClass` makes it an additive subgroup. The module `Mathlib.RingTheory.TwoSidedIdeal.Instances` adds the instance `instNonUnitalSubringClassTwoSidedIdeal`: a two-sided ideal is a non-unital subring (see the next section). The module `Mathlib.RingTheory.TwoSidedIdeal.BigOperators` proves that an ideal is closed under finite sums, with `TwoSidedIdeal.finsetSum_mem`, `TwoSidedIdeal.multisetSum_mem`, `TwoSidedIdeal.listSum_mem` and the forms for finitely supported functions `TwoSidedIdeal.finsuppSum_mem` and `TwoSidedIdeal.dfinsuppSum_mem`. It also has the product forms, such as `TwoSidedIdeal.finsetProd_mem`: a product with one factor in $I$ is in $I$.

The opposite ring $R^{\mathrm{op}}$ has the same two-sided ideals. The map `TwoSidedIdeal.op` and its inverse `TwoSidedIdeal.unop` express this, and `TwoSidedIdeal.opOrderIso` bundles them as an order isomorphism with `TwoSidedIdeal.mem_op_iff` for membership.

#### The lattice and the kernel

The module `Mathlib.RingTheory.TwoSidedIdeal.Lattice` gives `TwoSidedIdeal R` the structure `TwoSidedIdeal.instCompleteLattice`. Each operation comes from the lattice of congruences, and a lemma such as `TwoSidedIdeal.sup_ringCon` or `TwoSidedIdeal.inf_ringCon` records the link. The membership lemmas are the ones to use in proofs:

| Lean name | Statement |
|---|---|
| `TwoSidedIdeal.mem_bot` | $x \in \bot \iff x = 0$ |
| `TwoSidedIdeal.mem_top` | every $x$ is in $\top$ |
| `TwoSidedIdeal.mem_inf` | $x \in I \sqcap J \iff x \in I \wedge x \in J$ |
| `TwoSidedIdeal.mem_sup` | $x \in I \sqcup J \iff \exists\, y \in I,\ z \in J,\ y + z = x$ |
| `TwoSidedIdeal.mem_iInf` | $x \in \bigsqcap_i I_i \iff \forall i,\ x \in I_i$ |
| `TwoSidedIdeal.one_mem_iff` | $1 \in I \iff I = \top$ |

The module `Mathlib.RingTheory.TwoSidedIdeal.Kernel` defines the kernel `TwoSidedIdeal.ker f` of a homomorphism $f : R \to S$, with `TwoSidedIdeal.mem_ker` stating $x \in \ker f \iff f(x) = 0$.

**Theorem (Kernels and injectivity).** A ring homomorphism $f$ is injective if and only if $\ker f = 0$.

*Proof.* If $f$ is injective and $f(x) = 0 = f(0)$, then $x = 0$. Conversely, if $\ker f = 0$ and $f(x) = f(y)$, then $f(x - y) = 0$, so $x - y = 0$. $\square$

This is `TwoSidedIdeal.ker_eq_bot`. Every two-sided ideal is a kernel: `TwoSidedIdeal.ker_ringCon_mk'` states that $I$ is the kernel of the projection onto the quotient by its congruence.

#### Spans, images and comparison with `Ideal`

The module `Mathlib.RingTheory.TwoSidedIdeal.Operations` builds the ideal `TwoSidedIdeal.span s` generated by a set $s$. Its universal property is `TwoSidedIdeal.span_le`, and `TwoSidedIdeal.subset_span` and `TwoSidedIdeal.span_mono` are the basic facts. Induction on the span is `TwoSidedIdeal.span_induction`.

**Theorem (Elements of a span).** In a ring $R$ with unit, $z \in \operatorname{span}(s)$ if and only if $z$ is a finite sum of terms $\pm\, a x b$ with $a, b \in R$ and $x \in s$.

*Proof.* The set $T$ of such sums is an additive subgroup. It is closed under left and right multiplication, since $r (a x b) = (r a) x b$ and $(a x b) r = a x (b r)$. It contains $s$, since $x = 1 \cdot x \cdot 1$. So $T$ is a two-sided ideal that contains $s$, and $\operatorname{span}(s) \subseteq T$. Each term $a x b$ lies in every two-sided ideal that contains $x$, so $T \subseteq \operatorname{span}(s)$. $\square$

This is `TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure`, where the set of products is written `Set.univ * s * Set.univ`. The variant `TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure_nonunital` adds the terms $a x$, $x b$ and $x$ for a ring without unit.

The image and the preimage along a homomorphism are `TwoSidedIdeal.map` and `TwoSidedIdeal.comap`, with `TwoSidedIdeal.mem_comap`, `TwoSidedIdeal.comap_comap` and the monotonicity lemmas `TwoSidedIdeal.map_mono` and `TwoSidedIdeal.comap_le_comap`. A ring isomorphism gives the order isomorphism `RingEquiv.mapTwoSidedIdeal`.

A two-sided ideal is a left ideal, by the order embedding `TwoSidedIdeal.asIdeal : TwoSidedIdeal R →o Ideal R`, and a right ideal, by `TwoSidedIdeal.asIdealOpposite` into the left ideals of $R^{\mathrm{op}}$. In the other direction, `TwoSidedIdeal.fromIdeal` sends a left ideal to the two-sided ideal that it generates, and `TwoSidedIdeal.gc` states that the two maps form a Galois connection. A left ideal with the class `Ideal.IsTwoSided` becomes a two-sided ideal by `Ideal.toTwoSided`, and `TwoSidedIdeal.orderIsoIsTwoSided` identifies `TwoSidedIdeal R` with the left ideals that satisfy the class. For a commutative ring all three notions agree, and `TwoSidedIdeal.orderIsoIdeal` is the order isomorphism with `Ideal R`. The instances `TwoSidedIdeal.leftModule` and `TwoSidedIdeal.rightModule` make an ideal a module over $R$ and over $R^{\mathrm{op}}$.

#### Simple rings

**Definition (Simple ring).** A ring $R$ is simple if $R \ne 0$ and its only two-sided ideals are $0$ and $R$.

The module `Mathlib.RingTheory.SimpleRing.Defs` defines the class `IsSimpleRing R` with the field `IsSimpleRing.simple : IsSimpleOrder (TwoSidedIdeal R)`, and `isSimpleRing_iff` unfolds it. The order-theoretic form says that the lattice has exactly two elements. The module `Mathlib.RingTheory.SimpleRing.Basic` gives the elementary consequences. The constructor `IsSimpleRing.of_eq_bot_or_eq_top` proves simplicity from the dichotomy, and the instance `IsSimpleRing.instNontrivial` records $R \ne 0$.

**Theorem (Nonzero elements generate).** In a simple ring $R$ with unit, a two-sided ideal $I$ that contains a nonzero element $x$ contains $1$.

*Proof.* The ideal $I$ is not $0$, since $x \in I$. So $I = R$, and $1 \in I$. $\square$

This is `IsSimpleRing.one_mem_of_ne_zero_mem`, with the variant `IsSimpleRing.one_mem_of_ne_bot`. The same argument gives the main property of simple rings.

**Theorem (Homomorphisms from a simple ring).** Let $R$ be simple and $f : R \to S$ a ring homomorphism with $S \ne 0$. Then $f$ is injective.

*Proof.* The kernel of $f$ is a two-sided ideal. It does not contain $1$, since $f(1) = 1 \ne 0$ in $S$. So $\ker f \ne R$, hence $\ker f = 0$, and $f$ is injective by `TwoSidedIdeal.ker_eq_bot`. $\square$

The library calls this result `RingHom.injective`, with the variant `IsSimpleRing.injective_ringHom_or_subsingleton_codomain` for an arbitrary target. The converse holds too: `IsSimpleRing.iff_injective_ringHom` states that a nonzero ring is simple when every homomorphism to a nonzero ring is injective. The module `Mathlib.RingTheory.SimpleRing.Congr` transports the property: `IsSimpleRing.of_ringEquiv` along an isomorphism and `IsSimpleRing.of_surjective` along a surjection. It also has `isSimpleRing_iff_isTwoSided_imp`, the form with left ideals that satisfy `Ideal.IsTwoSided`.

The examples come next. A division ring is simple, by the instance `DivisionRing.isSimpleRing`: a nonzero ideal contains a unit. The module `Mathlib.RingTheory.SimpleRing.Matrix` has the instance `IsSimpleRing.matrix`: the ring $M_n(A)$ of square matrices over a simple ring $A$ is simple for $n \ge 1$. The opposite ring of a simple ring is simple, by `IsSimpleRing.instMulOpposite`.

**Theorem (Commutative simple rings).** A commutative ring is simple if and only if it is a field.

*Proof.* A field is a division ring, so it is simple. Conversely, let $R$ be commutative and simple, and let $x \ne 0$. The ideal $(x) = x R$ is two-sided, since $R$ is commutative, and it is nonzero. So $(x) = R$, and $x y = 1$ for some $y$. $\square$

This is `isSimpleRing_iff_isField` in `Mathlib.RingTheory.SimpleRing.Field`. The same module proves `IsSimpleRing.isField_center`: the center of a simple ring is a field. The proof applies the commutative argument to a central element $z \ne 0$: the ideal $z R$ is two-sided, so it is $R$, and the inverse of $z$ is central again. The module `Mathlib.RingTheory.SimpleRing.Principal` gives the instances that follow for a commutative simple ring: `IsDomain.of_isSimpleRing`, `IsPrincipalIdealRing.of_isSimpleRing` and `instIsSimpleOrderIdeal`. The module `Mathlib.RingTheory.SimpleRing.DivisionRing` treats the modules over a division ring: `DivisionRing.nonempty_linearEquiv_of_isSimpleModule` states that every simple module over a division ring $S$ is isomorphic to $S$.

#### Common errors

1. A learner uses `Ideal R` for an ideal of a noncommutative ring and then looks for the quotient ring. `Ideal R` is the type of left ideals, and `R ⧸ I` is a ring only under the class `Ideal.IsTwoSided`. Use `TwoSidedIdeal R`, or prove the class.
2. A learner proves membership in a two-sided ideal with lemmas about `Ideal`, such as `Ideal.mul_mem_left`. These lemmas apply to `Ideal`, not to `TwoSidedIdeal`. Use `TwoSidedIdeal.mul_mem_left` and `TwoSidedIdeal.mul_mem_right`, or pass through `TwoSidedIdeal.asIdeal`.
3. A learner expects a simple ring to have no nontrivial left ideals. The ring $M_2(k)$ is simple, but the matrices with zero second column form a nonzero proper left ideal. Simplicity is a condition on two-sided ideals only.

### Exercises

1. (A) Let $f : R \to S$ be a ring homomorphism. Prove that $\ker f$ is a two-sided ideal and that $\ker f = 0$ exactly when $f$ is injective.
2. (A) Prove that the intersection of a family of two-sided ideals is a two-sided ideal, and compare with `TwoSidedIdeal.mem_iInf`.
3. (B) Let $k$ be a field. Prove that $M_2(k)$ is simple: from a nonzero matrix in a two-sided ideal, produce each matrix unit $E_{ij}$ by multiplication on both sides.
4. (B) Prove that the center of a simple ring is a field.
5. (B) Give a left ideal of $M_2(k)$ that is not a two-sided ideal, and the two-sided ideal that it generates.
6. (C) Let $R$ be a simple ring and $S \ne 0$. Prove that every ring homomorphism $R \to S$ is injective, and deduce that a simple ring has no proper nonzero quotient ring.

### Reference

<?reference?>
