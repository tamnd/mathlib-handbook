---
title: The Picard group
kind: api
modules:
  - Mathlib.RingTheory.PicardGroup
  - Mathlib.RingTheory.LocalProperties.Invertible
explains:
  E2: [Module.Invertible, CommRing.Pic, CommRing.Pic.mk, CommRing.Pic.mk_eq_one_iff_free, CommRing.Pic.mk_tensor, CommRing.Pic.mapAlgebra, Submodule.unitsToPic, ClassGroup.equivPic, Module.Invertible.exists_finset_free_localization, Module.Invertible.of_localized_maximal]
  E1: auto
families: []
requires: [V10.C02, V10.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Picard group

### Overview

The class group of Section 1 is defined for a domain, through fractional ideals. The Picard group is defined for every commutative ring, through modules. An $R$-module $M$ is invertible when some module $N$ has $M \otimes_R N \cong R$. The isomorphism classes of invertible modules form a group under the tensor product, with unit $R$ and inverse the dual module. This group is the Picard group $\operatorname{Pic}(R)$.

For a domain, every invertible module is isomorphic to an invertible fractional ideal, and $\operatorname{Pic}(R)$ is the class group. In geometry, $\operatorname{Pic}(R)$ is the group of line bundles on $\operatorname{Spec} R$. This section describes the class of invertible modules, the group, its functoriality, the exact sequence with the units of submodules, and the comparison with the class group.

### The library around it

#### Invertible modules

The class `Module.Invertible R M` in `Mathlib.RingTheory.PicardGroup` says that the contraction map $M \otimes_R M^\vee \to R$, $m \otimes f \mapsto f(m)$, is bijective. Its field is `Module.Invertible.bijective`. This definition does not quantify over modules $N$, so it is a proposition about $M$ only.

| Lean name | Statement |
|---|---|
| `Module.Invertible.instProjective` | an invertible module is projective |
| `Module.Invertible.instFinite` | an invertible module is finitely generated |
| `Module.Invertible.instDual` | the dual of an invertible module is invertible |
| `Module.Invertible.instTensorProduct` | a tensor product of invertible modules is invertible |
| `Module.Invertible.congr` | a module isomorphic to an invertible one is invertible |
| `Module.Invertible.toModuleEnd_bijective` | $R \to \operatorname{End}_R(M)$ is bijective |
| `Module.Invertible.tmul_comm` | $m_1 \otimes m_2 = m_2 \otimes m_1$ in $M \otimes M$ |
| `Module.Invertible.free_iff_linearEquiv` | $M$ is free if and only if $M \cong R$ |
| `Module.Invertible.rank_eq_one` | a free invertible module has rank $1$ |
| `Module.Invertible.of_isLocalization` | invertibility is stable under localization |

The definition `Module.Invertible.linearEquivDual` turns an isomorphism $M \otimes N \cong R$ into an isomorphism $N \cong M^\vee$. So the inverse is unique, and the definition by the dual agrees with the definition by some $N$. The lemma `Module.Invertible.leftInverse_iff_rightInverse` says that for maps $f : M \to N$ and $g : N \to M$ of invertible modules, $g \circ f = \mathrm{id}$ if and only if $f \circ g = \mathrm{id}$.

**Theorem.** An invertible module is locally free of rank one. There are $r_1, \dots, r_k$ that generate the unit ideal such that each $M_{r_i}$ is free over $R_{r_i}$. This is `Module.Invertible.exists_finset_free_localization`.

*Proof sketch.* Let $\mathfrak p$ be a prime. Then $M_{\mathfrak p}$ is invertible over the local ring $R_{\mathfrak p}$, and finitely generated and projective. A finitely generated projective module over a local ring is free. It has rank one, since $M_{\mathfrak p} \otimes M_{\mathfrak p}^\vee \cong R_{\mathfrak p}$ and ranks multiply. An invertible module is finitely presented, so a basis of $M_{\mathfrak p}$ spreads out to an open set $D(r)$ with $r \notin \mathfrak p$. Finitely many such sets cover $\operatorname{Spec} R$. $\square$

The converse is in `Mathlib.RingTheory.LocalProperties.Invertible`. A finitely generated module that is invertible at each maximal ideal is invertible, `Module.Invertible.of_localized_maximal`, and `Module.Invertible.of_isLocalized_maximal` is the form for any choice of localizations. The same module proves `Module.FinitePresentation.of_finite_of_flat_of_rankAtStalk_constant`: a finitely generated flat module whose rank at each maximal ideal is the same number $n$ is finitely presented.

#### The group

The type `CommRing.Pic R` is the group of isomorphism classes of invertible $R$-modules. The class of $M$ is `CommRing.Pic.mk R M`, and an element of the group has an underlying module, given by `CommRing.Pic.AsModule`.

1. `CommRing.Pic.mk_eq_mk_iff`: two classes are equal if and only if the modules are isomorphic.
2. `CommRing.Pic.mk_tensor`: the class of $M \otimes N$ is the product of the classes, and `CommRing.Pic.mul_eq_tensor` is the same law read from the group.
3. `CommRing.Pic.mk_dual`: the class of $M^\vee$ is the inverse, and `CommRing.Pic.inv_eq_dual` is the same law read from the group.
4. `CommRing.Pic.mk_eq_one_iff_free`: the class of $M$ is $1$ if and only if $M$ is free.
5. `CommRing.Pic.subsingleton_iff`: the group is trivial if and only if every invertible module is free.

The group is trivial for a local ring, by the instance `CommRing.Pic.instSubsingletonOfIsLocalRing`, since a finitely generated projective module over a local ring is free. It is also trivial for a ring with finitely many maximal ideals, by `CommRing.Pic.instSubsingletonOfFiniteMaximalSpectrum`.

#### Functoriality

A ring map $f : R \to S$ gives the group map `CommRing.Pic.mapRingHom f`, which sends $M$ to $S \otimes_R M$. For an $R$-algebra $A$ the same map is `CommRing.Pic.mapAlgebra R A`. The lemmas `CommRing.Pic.mapRingHom_id` and `CommRing.Pic.mapRingHom_comp_mapRingHom` give functoriality, and `CommRing.Pic.functor` is the functor from commutative semirings to commutative groups. The relative Picard group `CommRing.relPic R A` is the kernel of `mapAlgebra R A`: the classes that become trivial over $A$. It is the whole group when $\operatorname{Pic}(A)$ is trivial, `CommRing.relPic_eq_top`.

#### Units of submodules and the exact sequence

Let $A$ be an $R$-algebra in which $R$ acts faithfully, for instance the fraction field of a domain. The submodules of $A$ form a monoid under multiplication. A unit $I$ of this monoid has an inverse $J$ with $IJ = R$, and it is projective, `Submodule.projective_of_isUnit`. The map `Submodule.unitsToPic R A` sends $I$ to its class in $\operatorname{Pic}(R)$.

**Theorem.** The sequence

$$A^\times \to (\text{units of submodules of } A) \to \operatorname{Pic}(R) \to \operatorname{Pic}(A)$$

is exact. The first map sends $a$ to $Ra$. These are `Submodule.mulExact_unitsMap_spanSingleton_unitsToPic` and `Submodule.mulExact_unitsToPic_mapAlgebra`. The kernel and the image of the middle map are `Submodule.ker_unitsToPic` and `Submodule.range_unitsToPic`, and `Submodule.unitsQuotEquivRelPic` is the induced isomorphism of the quotient with `CommRing.relPic R A`.

*Proof sketch.* A unit $I$ maps to $1$ if and only if $I \cong R$ as an $R$-module. An isomorphism $R \to I$ sends $1$ to some $a$ with $I = Ra$, and $a$ is a unit of $A$ because $I$ is invertible. For exactness at $\operatorname{Pic}(R)$, the module $A \otimes_R I$ is $AI = A$ for a unit $I$. Conversely, an isomorphism $A \otimes_R M \cong A$ embeds $M$ into $A$ as an invertible submodule. $\square$

For a domain $R$ with fraction field $K$, the group $\operatorname{Pic}(K)$ is trivial and the units of submodules of $K$ are the invertible fractional ideals. So the sequence gives the isomorphism `ClassGroup.equivPic R` of the class group with the Picard group. In particular, `Module.Invertible.exists_linearEquiv_ideal` says that every invertible module over a domain is isomorphic to an ideal. For a Dedekind domain every nonzero fractional ideal is invertible, so $\operatorname{Pic}(R)$ is the group of nonzero fractional ideals modulo principal ones.

#### Common errors

1. `Module.Invertible R M` is a proposition. To use $M^\vee$ as the inverse, use `CommRing.Pic.mk_dual`, or the isomorphism `Module.Invertible.linearEquivDual` for a given $N$.
2. `CommRing.Pic R` is a group of classes. To get a module from an element, use `CommRing.Pic.AsModule`, and `CommRing.Pic.mk_self` to go back.
3. `ClassGroup.equivPic` needs `IsDomain R`. For a ring with zero divisors, the Picard group is the right invariant, and the class group is not defined.

### Exercises

1. (A) Show that $\operatorname{Pic}(k) = 1$ for a field $k$ and $\operatorname{Pic}(\mathbb{Z}) = 1$.
2. (A) Let $M$ be invertible. Show that $M \otimes_R M^\vee \cong R$ from the definition, and deduce that $\operatorname{End}_R(M) \cong R$.
3. (B) Let $R = \mathbb{Z}[\sqrt{-5}]$ and $I = (2, 1 + \sqrt{-5})$. Show that $I$ is an invertible module that is not free, and that $I \otimes_R I \cong R$.
4. (B) Show that $\operatorname{Pic}(R \times S) \cong \operatorname{Pic}(R) \times \operatorname{Pic}(S)$.
5. (B) Show that an invertible module over a ring with finitely many maximal ideals is free.
6. (C) Let $R$ be a domain with fraction field $K$. Use the exact sequence to show that $\operatorname{Pic}(R)$ is the group of invertible fractional ideals modulo the principal ones, and compare with `ClassGroup.equivPic`.

### Reference

<?reference?>
