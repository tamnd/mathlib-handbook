---
title: Non-unital subrings and subsemirings
kind: api
modules:
  - Mathlib.RingTheory.NonUnitalSubsemiring.Defs
  - Mathlib.RingTheory.NonUnitalSubsemiring.Basic
  - Mathlib.RingTheory.NonUnitalSubring.Defs
  - Mathlib.RingTheory.NonUnitalSubring.Basic
explains:
  E2: [NonUnitalSubring.mem_closure_iff, NonUnitalSubsemiring.mem_closure_iff, NonUnitalSubring.mem_iSup_of_directed, NonUnitalRingHom.eqOn_set_closure, NonUnitalSubring.closure_le_centralizer_centralizer, NonUnitalSubring.isMulCommutative_closure]
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

## Non-unital subrings and subsemirings

### Overview

An ideal $I$ of a ring $R$ is closed under addition, negation and multiplication, but it does not contain $1$ unless $I = R$. So an ideal is not a subring in the sense of Volume 6. It is a *non-unital subring*: an additive subgroup that is closed under multiplication, with no condition on the unit. The same notion covers the ring $2\mathbb{Z}$, the ring of functions with compact support on $\mathbb{R}$, and the continuous functional calculus of operator algebras, where the rings have no unit at all.

This section explains the two lattices that Mathlib builds for this notion: `NonUnitalSubsemiring R` for a non-unital semiring and `NonUnitalSubring R` for a non-unital ring. Their API copies the API of `Subsemiring` and `Subring` term by term, so a reader who knows one knows the other. The new results are about closures: the closure of a set is described by sums of products, and it lies in the double centralizer. The previous section used these structures through the instance `instNonUnitalSubringClassTwoSidedIdeal`.

### The library around it

#### The structures and the classes

**Definition (Non-unital subsemiring, non-unital subring).** Let $R$ be a non-unital semiring. A non-unital subsemiring of $R$ is a subset that contains $0$ and is closed under addition and multiplication. If $R$ is a non-unital ring, a non-unital subring is a non-unital subsemiring that is closed under negation.

The module `Mathlib.RingTheory.NonUnitalSubsemiring.Defs` defines the structure `NonUnitalSubsemiring R`. It extends `AddSubmonoid R` and `Subsemigroup R`, and the projections are `NonUnitalSubsemiring.toAddSubmonoid` and `NonUnitalSubsemiring.toSubsemigroup`. The module `Mathlib.RingTheory.NonUnitalSubring.Defs` defines `NonUnitalSubring R`, which extends `NonUnitalSubsemiring R` by closure under negation. Its projections are `NonUnitalSubring.toNonUnitalSubsemiring`, `NonUnitalSubring.toAddSubgroup` and `NonUnitalSubring.toSubsemigroup`, and each projection is injective and monotone (`NonUnitalSubring.toAddSubgroup_injective`, `NonUnitalSubring.toAddSubgroup_mono`, and so on). The ring needs only `[NonUnitalNonAssocRing R]`, so associativity is not required either.

Each structure comes with a class for types of subsets, in the pattern of the whole library: `NonUnitalSubsemiringClass S R` and `NonUnitalSubringClass S R`. The class lets a lemma apply at once to subrings, ideals, subalgebras and two-sided ideals. A term of a type with the class becomes a ring in its own right: `NonUnitalSubringClass.toNonUnitalRing` and `NonUnitalSubringClass.toNonUnitalCommRing` give the instances, and `NonUnitalSubringClass.subtype` is the inclusion as a non-unital ring homomorphism. The instance `NonUnitalSubsemiringClass.noZeroDivisors` passes the absence of zero divisors to a subset.

The membership lemmas have the usual names: `NonUnitalSubring.zero_mem`, `NonUnitalSubring.add_mem`, `NonUnitalSubring.neg_mem`, `NonUnitalSubring.sub_mem`, `NonUnitalSubring.mul_mem` and `NonUnitalSubring.zsmul_mem`. Two lemmas in the root namespace treat signs: `neg_mul_mem` and `mul_neg_mem`. The coercions to the ring compute with `NonUnitalSubring.val_add`, `NonUnitalSubring.val_mul`, `NonUnitalSubring.val_neg` and `NonUnitalSubring.val_zero`. Two substructures with the same elements are equal by `NonUnitalSubring.ext`. The constructor `NonUnitalSubring.mk'` builds a non-unital subring from a set with a subsemigroup and an additive subgroup that have this set as carrier, and `NonUnitalSubring.copy` replaces the carrier by an equal set with better definitional behaviour. The map `NonUnitalSubring.inclusion` is the inclusion of one substructure in a larger one.

#### The lattice and the closure

The modules `Mathlib.RingTheory.NonUnitalSubsemiring.Basic` and `Mathlib.RingTheory.NonUnitalSubring.Basic` give both types a complete lattice, `NonUnitalSubsemiring.instCompleteLattice` and `NonUnitalSubring.instCompleteLattice`. The bottom element is $\{0\}$, by `NonUnitalSubring.mem_bot`, and the top element is $R$, by `NonUnitalSubring.mem_top`. Infima are intersections, by `NonUnitalSubring.mem_inf`, `NonUnitalSubring.mem_iInf` and `NonUnitalSubring.mem_sInf`. The closure `NonUnitalSubring.closure s` is the smallest non-unital subring that contains $s$. The function `NonUnitalSubring.gi` states that the closure and the coercion to sets form a Galois insertion, so `NonUnitalSubring.closure_le`, `NonUnitalSubring.subset_closure`, `NonUnitalSubring.closure_mono` and `NonUnitalSubring.closure_eq` hold. The general description `NonUnitalSubring.mem_closure` says that $x$ lies in the closure when it lies in every non-unital subring that contains $s$.

**Theorem (Elements of a closure).** Let $s$ be a subset of a non-unital ring $R$. The non-unital subring generated by $s$ is the additive subgroup generated by the subsemigroup generated by $s$. So its elements are the finite sums $\sum \pm x_1 x_2 \cdots x_k$ of products of elements of $s$ with $k \ge 1$.

*Proof.* Let $M$ be the subsemigroup generated by $s$, the set of nonempty products of elements of $s$, and let $A$ be the additive subgroup generated by $M$. The set $A$ is closed under multiplication: a product of two sums of elements of $\pm M$ is, by distributivity, a sum of products of two elements of $\pm M$, and $M$ is closed under products. So $A$ is a non-unital subring that contains $s$, and it contains the closure. Conversely, every non-unital subring that contains $s$ contains $M$ and then $A$. $\square$

This is `NonUnitalSubring.mem_closure_iff`. For a semiring the same argument works without signs, and `NonUnitalSubsemiring.mem_closure_iff` states the result with `AddSubmonoid.closure`. The equation `NonUnitalSubsemiring.closure_addSubmonoid_closure` shows that closing first under addition changes nothing, and `Subsemigroup.nonUnitalSubsemiringClosure_eq_closure` is the form that starts from a subsemigroup. The induction principles `NonUnitalSubring.closure_induction` and `NonUnitalSubring.closure_induction₂` prove a property of the elements of a closure from its cases $s$, $0$, sum, negation and product. The rules `NonUnitalSubring.closure_union`, `NonUnitalSubring.closure_iUnion`, `NonUnitalSubring.closure_sUnion`, `NonUnitalSubring.closure_empty` and `NonUnitalSubring.closure_univ` give the closure of a union, of the empty set and of the whole ring.

**Theorem (Directed suprema).** Let $(S_i)_{i \in \iota}$ be a nonempty directed family of non-unital subrings. Then $x \in \bigsqcup_i S_i$ if and only if $x \in S_i$ for some $i$.

*Proof.* The union $U = \bigcup_i S_i$ contains each $S_i$, and it is contained in the supremum. It is a non-unital subring: two elements $x \in S_i$ and $y \in S_j$ lie in a common $S_k$ with $S_i, S_j \le S_k$, since the family is directed, so $x + y$, $-x$ and $x y$ lie in $S_k \subseteq U$, and $0 \in U$ since $\iota$ is nonempty. So the supremum is $U$. $\square$

This is `NonUnitalSubring.mem_iSup_of_directed`, with the set form `NonUnitalSubring.mem_sSup_of_directedOn`.

#### Maps, ranges and products

A non-unital ring homomorphism $f : R \to_{n+*} S$ moves the substructures. The image is `NonUnitalSubring.map f` and the preimage is `NonUnitalSubring.comap f`, with `NonUnitalSubring.mem_map`, `NonUnitalSubring.mem_comap`, `NonUnitalSubring.map_map`, `NonUnitalSubring.comap_comap` and the Galois connection `NonUnitalSubring.gc_map_comap`. The image preserves suprema (`NonUnitalSubring.map_sup`, `NonUnitalSubring.map_iSup`) and the preimage preserves infima (`NonUnitalSubring.comap_inf`, `NonUnitalSubring.comap_iInf`). An injective map gives an isomorphism with the image, `NonUnitalSubring.equivMapOfInjective`, and a ring isomorphism gives `RingEquiv.nonUnitalSubringCongr`.

The range of $f$ is the non-unital subring `NonUnitalRingHom.range f`, with `NonUnitalRingHom.mem_range` and `NonUnitalRingHom.range_eq_map`. The map `NonUnitalRingHom.rangeRestrict` corestricts $f$ to its range, and `NonUnitalRingHom.rangeRestrict_surjective` states that it is onto. A left inverse gives an isomorphism with the range, `RingEquiv.ofLeftInverse'`. For semirings the names carry the letter s: `NonUnitalRingHom.srange`, `NonUnitalRingHom.srangeRestrict` and `RingEquiv.sofLeftInverse'`. The set where two maps agree is `NonUnitalRingHom.eqLocus f g`, a non-unital subring.

**Theorem (Agreement on a closure).** If two non-unital ring homomorphisms $f, g : R \to S$ agree on a set $s$, then they agree on the non-unital subring generated by $s$.

*Proof.* The set $\{x : f(x) = g(x)\}$ is a non-unital subring, since $f$ and $g$ preserve $0$, sums, negatives and products. It contains $s$, so it contains the closure of $s$. $\square$

This is `NonUnitalRingHom.eqOn_set_closure`, and `NonUnitalRingHom.eqOn_sclosure` is the semiring form. The product of two non-unital subrings is `NonUnitalSubring.prod`, with `NonUnitalSubring.mem_prod` and the isomorphism `NonUnitalSubring.prodEquiv` of the product with the product of rings.

#### Centers and centralizers

The center `NonUnitalSubring.center R` is the set of elements that commute with every element, by `NonUnitalSubring.mem_center_iff`. It is a commutative ring, by the instance `NonUnitalSubring.center.instNonUnitalCommRing`, and `NonUnitalSubring.center_eq_top` states that it is the whole ring when $R$ is commutative. The centralizer `NonUnitalSubring.centralizer s` of a set $s$ is the set of elements that commute with each element of $s$, with `NonUnitalSubring.mem_centralizer_iff`. A larger set has a smaller centralizer, by `NonUnitalSubring.centralizer_le`.

**Theorem (Double centralizer).** For every subset $s$ of a non-unital ring, the closure of $s$ is contained in the centralizer of the centralizer of $s$.

*Proof.* Each element of $s$ commutes with each element of the centralizer $C(s)$. So $s \subseteq C(C(s))$. The set $C(C(s))$ is a non-unital subring, so it contains the closure of $s$. $\square$

This is `NonUnitalSubring.closure_le_centralizer_centralizer`. A consequence is `NonUnitalSubring.isMulCommutative_closure`: if the elements of $s$ commute pairwise, then the closure of $s$ is commutative. Indeed, $s \subseteq C(s)$, so $C(C(s)) \subseteq C(s)$, and the closure lies in $C(s) \cap C(C(s))$, whose elements commute with each other. The instance `NonUnitalSubring.instIsMulCommutative_closure` and the lemma `NonUnitalSubring.isMulCommutative_iSup` are the forms for instance search and for directed suprema. Each of these results has a twin in the namespace `NonUnitalSubsemiring`.

#### Common errors

1. A learner looks for a lemma that $1$ lies in a non-unital subring. There is none: the structure has no unit, and $2\mathbb{Z}$ does not contain $1$. To use the unit of $R$, pass to `Subring R`, which has more structure.
2. A learner proves a closure property for one kind of substructure at a time. The lemmas stated for the class, such as `neg_mul_mem`, apply to every type with `NonUnitalSubringClass` or `MulMemClass`, so one proof covers subrings, non-unital subrings and two-sided ideals.
3. A learner writes `NonUnitalRingHom.range` for a homomorphism of non-unital semirings and gets an error. The range in a semiring is `NonUnitalRingHom.srange`, with the letter s, since `NonUnitalRingHom.range` needs negation in the target.

### Exercises

1. (A) Prove that $2\mathbb{Z}$ is a non-unital subring of $\mathbb{Z}$ that is not a subring.
2. (A) Describe the non-unital subring of $\mathbb{Z}$ generated by $\{6, 10\}$. Hint: use `NonUnitalSubring.mem_closure_iff`.
3. (B) Prove that the union of a chain of non-unital subrings is a non-unital subring, and that the union of two arbitrary ones need not be one.
4. (B) Let $R$ be the ring of $2 \times 2$ upper triangular matrices over a field. Compute its center.
5. (B) Prove that the center of a non-unital ring is the centralizer of the whole ring.
6. (C) Let $s$ be a set of pairwise commuting elements of a ring. Prove that the subring generated by $s$ is commutative, and compare with `NonUnitalSubring.isMulCommutative_closure`.

### Reference

<?reference?>
