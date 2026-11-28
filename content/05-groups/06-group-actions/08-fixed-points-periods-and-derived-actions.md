---
title: Fixed points, periods and derived actions
kind: api
modules:
  - Mathlib.GroupTheory.GroupAction.FixedPoints
  - Mathlib.GroupTheory.GroupAction.FixingSubgroup
  - Mathlib.GroupTheory.GroupAction.Period
  - Mathlib.GroupTheory.GroupAction.Pointwise
  - Mathlib.GroupTheory.GroupAction.ConjAct
  - Mathlib.GroupTheory.GroupAction.IterateAct
  - Mathlib.GroupTheory.GroupAction.DomAct.Basic
  - Mathlib.GroupTheory.GroupAction.DomAct.ActionHom
explains:
  E2: [MulAction.smul_fixedBy, MulAction.not_commute_of_disjoint_movedBy_preimage, fixingSubgroup, fixingSubgroup_fixedPoints_gc, MulAction.period_dvd_orderOf, image_smul_set, ConjAct.normal_of_characteristic_of_normal, IterateMulAct, DomMulAct, DomMulAct.smul_apply]
  E1: auto
families: []
requires: [V01, V05.C02, V05.C03, V05.C04, V05.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Fixed points, periods and derived actions

### Overview

Let a group $G$ act on a set $X$. Each element $g$ has a set of fixed points $\operatorname{Fix}(g) = \{x : g \cdot x = x\}$, and each set $S \subseteq X$ has a fixing subgroup, the group of the $g$ that fix every point of $S$. These two operations are the two halves of a Galois connection between the subsets of $X$ and the subgroups of $G$. The same pattern appears in Galois theory, where a group of automorphisms of a field acts on the field. Each point $x$ also has a period under $g$: the least $n > 0$ with $g^n \cdot x = x$.

This section describes the library of these notions, in the modules `Mathlib.GroupTheory.GroupAction.FixedPoints`, `Mathlib.GroupTheory.GroupAction.FixingSubgroup` and `Mathlib.GroupTheory.GroupAction.Period`. It also describes four modules that build new actions from old ones: the action on images and preimages of sets under an equivariant map, the conjugation action `ConjAct`, the action of $\mathbb{N}$ by the iterates of one map, and the action on functions through the domain, `DomMulAct`.

The fixed points and the stabilizers of the first section of this chapter, the conjugation action of the second section, and the equivariant maps of the fifth section are the background. The period uses the order of an element and the exponent from Chapter 4.

### The library around it

#### Fixed points of one element

The set `MulAction.fixedBy α m` is the set of points of $\alpha$ that $m$ fixes, with the membership lemma `MulAction.mem_fixedBy`. The set `MulAction.fixedPoints M α` is the set of points that all of $M$ fixes. Both are defined in an earlier module of the action library. The module `Mathlib.GroupTheory.GroupAction.FixedPoints` gives the algebra of `fixedBy`. The basic facts are: $\operatorname{Fix}(1)$ is everything, `MulAction.fixedBy_one_eq_univ`; $\operatorname{Fix}(g^{-1}) = \operatorname{Fix}(g)$, `MulAction.fixedBy_inv`; $\operatorname{Fix}(m_1) \cap \operatorname{Fix}(m_2) \subseteq \operatorname{Fix}(m_1 m_2)$, `MulAction.fixedBy_mul`; and $\operatorname{Fix}(g) \subseteq \operatorname{Fix}(g^j)$ for each integer $j$, `MulAction.fixedBy_subset_fixedBy_zpow`. For a faithful action, $\operatorname{Fix}(m)$ is everything only for $m = 1$, `MulAction.fixedBy_eq_univ_iff_eq_one`. A point is fixed by $g$ exactly when its minimal period under the map $x \mapsto g \cdot x$ is $1$, `MulAction.minimalPeriod_eq_one_iff_fixedBy`.

**Proposition.** For $g, h \in G$, $h \cdot \operatorname{Fix}(g) = \operatorname{Fix}(h g h^{-1})$.

*Proof.* If $g \cdot x = x$, then $(h g h^{-1}) \cdot (h \cdot x) = h \cdot (g \cdot x) = h \cdot x$. So $h \cdot \operatorname{Fix}(g) \subseteq \operatorname{Fix}(h g h^{-1})$. The same argument with $h^{-1}$ and $h g h^{-1}$ gives the other inclusion. $\square$

The library form is `MulAction.smul_fixedBy`. So conjugate elements have fixed point sets of the same size, and the number of fixed points is a class function.

The complement $\operatorname{Fix}(g)^c$ is the set of points that $g$ moves, the support of $g$. The library does not give it a name of its own: the statements write `(MulAction.fixedBy α g)ᶜ`. A set $s$ is stable under $g$ when $g \cdot s = s$. The library expresses this as `s ∈ MulAction.fixedBy (Set α) g`, with the action of $G$ on sets, and `MulAction.set_mem_fixedBy_iff` unfolds it to $\forall x, g \cdot x \in s \iff x \in s$. Each subset of $\operatorname{Fix}(g)$ and each superset of the support is stable, by `MulAction.set_mem_fixedBy_of_subset_fixedBy` and `MulAction.set_mem_fixedBy_of_movedBy_subset`.

If $g$ and $h$ commute, then $h$ maps $\operatorname{Fix}(g)$ to itself, by the proposition, because $h g h^{-1} = g$. This is `MulAction.fixedBy_mem_fixedBy_of_commute`, and `MulAction.movedBy_mem_fixedBy_of_commute` is the same for the support. The contrapositive gives a test for noncommuting elements.

**Proposition.** Let the action be faithful and let $g \ne 1$. If the support of $g$ is disjoint from its image under $h$, then $g$ and $h$ do not commute.

*Proof.* Let $U$ be the support of $g$. If $g$ and $h$ commute, then $h \cdot U = U$. So $U$ is disjoint from itself, and $U = \emptyset$. Then $g$ fixes every point, and $g = 1$ because the action is faithful. $\square$

The library form is `MulAction.not_commute_of_disjoint_movedBy_preimage`. For the action of a monoid on itself by left multiplication, no element except $1$ has a fixed point when the monoid is right cancellative: `MulAction.fixedBy_mul_eq_empty_iff`. Equivariant maps preserve fixed points, `MulActionHom.map_mem_fixedBy` and `MulActionHom.map_mem_fixedPoints`.

#### Fixing subgroups

For a set $s \subseteq \alpha$, `fixingSubgroup M s` is the subgroup of the $m \in M$ with $m \cdot y = y$ for all $y \in s$, and `fixingSubmonoid M s` is the same for a monoid. The membership lemma is `mem_fixingSubgroup_iff`, and `mem_fixingSubgroup_iff_subset_fixedBy` states it as $s \subseteq \operatorname{Fix}(m)$. The fixing subgroup of one point is its stabilizer.

The operation reverses inclusions, `fixingSubgroup_antitone`. It sends unions to intersections, `fixingSubgroup_union` and `fixingSubgroup_iUnion`, and the empty set to the whole group, `fixingSubgroup_empty`. In the other direction, the fixed points of a subgroup $P$ are `MulAction.fixedPoints P α`. The fixed points of $P \sqcup Q$ are the common fixed points, `fixedPoints_subgroup_sup`, and the same holds for a family, `fixedPoints_subgroup_iSup`. All these facts follow from one statement.

**Proposition.** For a set $s \subseteq \alpha$ and a subgroup $P \le G$, $s \subseteq \operatorname{Fix}(P)$ if and only if $P \le \operatorname{Fix}(s)$, where $\operatorname{Fix}(s)$ is the fixing subgroup.

*Proof.* Both sides say that $p \cdot y = y$ for all $p \in P$ and all $y \in s$. $\square$

The library form is `fixingSubgroup_fixedPoints_gc`. It is a Galois connection between sets and the order dual of the subgroups, because both maps reverse the order. The monoid version is `fixingSubmonoid_fixedPoints_gc`. The general theory of Galois connections then gives the antitone and union lemmas.

The fixing subgroup of a complement controls the support. An element fixes $s^c$ exactly when its support is in $s$, `mem_fixingSubgroup_compl_iff_movedBy_subset`. Then the group fixing $s^c$ moves the points of $s$ only inside $s$: `orbit_fixingSubgroup_compl_subset` says that the orbit of $a \in s$ under this group is in $s$.

#### Periods

For $m \in M$ and $a \in \alpha$, the number `MulAction.period m a` is the least $n > 0$ with $m^n \cdot a = a$, and $0$ when no such $n$ exists. It is the minimal period of $a$ under the map $x \mapsto m \cdot x$. The definition is in the dynamics library, and the module `Mathlib.GroupTheory.GroupAction.Period` relates it to the order and the exponent. The period is $1$ exactly at fixed points, `MulAction.period_eq_one_iff`, and the period of $1$ is $1$, `MulAction.period_one`. For a group, $g$ and $g^{-1}$ have the same periods, `MulAction.period_inv`.

The period has the two properties of a minimum. If $0 < n$ and $m^n \cdot a = a$, then the period is at most $n$, `MulAction.period_le_of_fixed`, and it is positive, `MulAction.period_pos_of_fixed`. If $0 < n$ is less than the period, then $m^n \cdot a \ne a$, `MulAction.pow_smul_ne_of_lt_period`. The lemma `MulAction.le_period` is the converse form.

**Proposition.** The period of $a$ under $m$ divides the order of $m$.

*Proof.* Let $k$ be the order of $m$. Then $m^k \cdot a = 1 \cdot a = a$, so $k$ is a period of $a$. Each period of a point is a multiple of the minimal period, by division with remainder. If $k = 0$, the statement is true because each number divides $0$. $\square$

The library form is `MulAction.period_dvd_orderOf`. With the exponent of Chapter 4 the same argument gives `MulAction.period_dvd_exponent`. If the order of $m$ is positive, the period is positive and at most the order, `MulAction.period_pos_of_orderOf_pos` and `MulAction.period_le_orderOf`. If the exponent of $M$ is positive, then the periods of $m$ are bounded, `MulAction.period_bounded_of_exponent_pos`.

#### Images and preimages of sets

An equivariant map $f$ commutes with the action on sets: $f(c \cdot s) = c \cdot f(s)$. This is `image_smul_set`, for each type of functions with a `MulActionHomClass` instance. The proof is one line: an element of $f(c \cdot s)$ is $f(c \cdot x) = c \cdot f(x)$ for some $x \in s$. For preimages only one inclusion holds in general, $c \cdot f^{-1}(t) \subseteq f^{-1}(c \cdot t)$, `smul_preimage_set_subset`. It is an equality when $c$ is a unit, `IsUnit.preimage_smul_set`, and so always for a group, `Group.preimage_smul_set`. The lemma `Set.MapsTo.smul_set` says that if $f$ maps $s$ into $t$, then it maps $c \cdot s$ into $c \cdot t$. Each lemma has a version with the suffix `ₛₗ` for a map that is equivariant over a map $\sigma$ of the acting monoids, such as `image_smul_setₛₗ`.

#### The conjugation action

The type `ConjAct G` and its action $g \cdot h = g h g^{-1}$ are the subject of the second section of this chapter. The module `Mathlib.GroupTheory.GroupAction.ConjAct` has more. The orbits are the conjugacy classes, `ConjAct.orbit_eq_carrier_conjClasses` and `ConjAct.mem_orbit_conjAct`, and the orbit relation is `IsConj`, `ConjAct.orbitRel_conjAct`. The fixed points are the center, `ConjAct.fixedPoints_eq_center`. The lemma `ConjAct.toConjAct_smul_eq_mulAut_conj` links the action to the inner automorphism `MulAut.conj`.

For a monoid $M$, the units act on $M$ by conjugation, `ConjAct.unitsMulDistribMulAction`, and `unitsCentralizerEquiv` identifies the stabilizer of a unit $x$ with the units of the centralizer of $x$. A normal subgroup $H$ is stable under conjugation, so `ConjAct G` acts on $H$, `ConjAct.Subgroup.conjMulDistribMulAction`. As a homomorphism, this is `MulAut.conjNormal : G →* MulAut H`, with `MulAut.conjNormal_apply`.

**Proposition.** A characteristic subgroup $K$ of a normal subgroup $H$ of $G$ is normal in $G$.

*Proof.* For $g \in G$, conjugation by $g$ maps $H$ to $H$, because $H$ is normal. So it restricts to an automorphism of $H$. A characteristic subgroup is stable under all automorphisms of $H$, so $g K g^{-1} = K$. $\square$

The library form is `ConjAct.normal_of_characteristic_of_normal`, with `Subgroup.Characteristic` for the hypothesis on $K$. The subgroup $K$ lives in $H$, so the conclusion is about its image `Subgroup.map H.subtype K`.

#### The action of the iterates of a map

For a map $f : \alpha \to \alpha$, the type `IterateMulAct f` is a copy of $\mathbb{N}$ that acts on $\alpha$ by $n \cdot x = f^{[n]}(x)$, the $n$-th iterate. The lemma `IterateMulAct.mk_smul` states this. It is a commutative monoid, `IterateMulAct.instCommMonoid`, written multiplicatively, so that $n \cdot (k \cdot x) = (n + k) \cdot x$ is the action law for the product of `IterateMulAct.mk n` and `IterateMulAct.mk k`. The additive copy `IterateAddAct f` is the same with $\mathbb{N}$ as an additive monoid. These types let the general lemmas about orbits, periods and fixed points apply to a single map. A copy of $\mathbb{N}$ for each $f$ is needed, because $\mathbb{N}$ itself can carry only one action on $\alpha$.

#### Actions through the domain

If $M$ acts on $\alpha$, then it acts on functions $f : \alpha \to \beta$ by precomposition: $(c \cdot f)(a) = f(c \cdot a)$. This is a right action. The type `DomMulAct M`, with the notation `Mᵈᵐᵃ`, is a copy of the opposite monoid of $M$ that carries this action. The equivalence `DomMulAct.mk : M ≃ Mᵈᵐᵃ` reverses products, `DomMulAct.mk_mul` states $\operatorname{mk}(a b) = \operatorname{mk}(b) \operatorname{mk}(a)$, and `DomMulAct.smul_apply` states

$$(c \cdot f)(a) = f(\operatorname{mk}^{-1}(c) \cdot a).$$

The reversal is forced. For $f : \alpha \to \beta$, $(\operatorname{mk}(a) \cdot (\operatorname{mk}(b) \cdot f))(x) = f(b \cdot (a \cdot x)) = f((b a) \cdot x)$. So the product $\operatorname{mk}(a) \operatorname{mk}(b)$ must act as $\operatorname{mk}(b a)$.

A copy is needed because `Mᵐᵒᵖ` already has an action on $M \to M$ through the codomain when $M$ acts on itself on the right, and two instances on one type would clash. The action on functions is faithful when the action on $\alpha$ is faithful and $\beta$ has two elements, `DomMulAct.instFaithfulSMulForallOfNontrivial`. It commutes with every action through the codomain, by the instances `DomMulAct.instSMulCommClassForall` and `DomMulAct.instSMulCommClassForall_1`. The same action exists on monoid homomorphisms when $M$ acts by a `MulDistribMulAction`, `DomMulAct.smul_monoidHom_apply`. The module `Mathlib.GroupTheory.GroupAction.DomAct.ActionHom` gives it on equivariant maps `α →[N] β` when the actions of $M$ and $N$ on $\alpha$ commute, `DomMulAct.smul_mulActionHom_apply`.

#### Common errors

1. The support of $g$ has no name of its own in this library. Lemma names use the word "movedBy" for it, but the set itself is `(MulAction.fixedBy α g)ᶜ`. For permutations, the support is `Equiv.Perm.support`, which is a `Finset`, not a set.
2. `MulAction.period m a` is $0$ when no positive power of $m$ fixes $a$. A lemma with the conclusion $0 <$ `MulAction.period m a` needs a hypothesis such as a positive order of $m$.
3. In `DomMulAct M` the product is reversed. A rewrite with `DomMulAct.mk_mul` swaps the factors, and a direct proof by `rfl` across `DomMulAct.mk` often fails, because `DomMulAct.mk` is an equivalence and not the identity.

### Exercises

1. (A) Let $G$ act on a finite set. Show that the function $g \mapsto |\operatorname{Fix}(g)|$ is constant on conjugacy classes.
2. (A) Show that $\operatorname{Fix}(g) \subseteq \operatorname{Fix}(g^j)$ for all $j \in \mathbb{Z}$, and that equality holds when $j$ is prime to the order of $g$.
3. (A) Let $G$ act on $\alpha$ and let $s \subseteq \alpha$. Show that the fixing subgroup of $g \cdot s$ is $g \operatorname{Fix}(s) g^{-1}$.
4. (B) Show that the fixing subgroup of $\operatorname{Fix}(\operatorname{Fix}(s))$ is the fixing subgroup of $s$, for each set $s$, using only the Galois connection.
5. (B) Let $g \in G$ have order $n$, and let $a$ be a point. Show that the orbit of $a$ under the cyclic group generated by $g$ has `MulAction.period g a` elements.
6. (C) Let $f : \alpha \to \alpha$ be a map. Describe the orbits of `IterateMulAct f` when $f$ is a bijection of a finite set, and show that the periods of the points are the lengths of the cycles of $f$.

### Reference

<?reference?>
