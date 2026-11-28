---
title: Faithfully flat algebras and flatness criteria
kind: api
modules:
  - Mathlib.RingTheory.Flat.CategoryTheory
  - Mathlib.RingTheory.Flat.Domain
  - Mathlib.RingTheory.Flat.Equalizer
  - Mathlib.RingTheory.Flat.EquationalCriterion
  - Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
  - Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
  - Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
  - Mathlib.RingTheory.Flat.IsBaseChange
  - Mathlib.RingTheory.Flat.Localization
  - Mathlib.RingTheory.Flat.LocallyFree
  - Mathlib.RingTheory.Flat.Rank
explains:
  E2: [Module.FaithfullyFlat.iff_flat_and_proper_ideal, Module.FaithfullyFlat.tensorProduct_mk_injective, Ideal.comap_map_eq_self_of_faithfullyFlat, PrimeSpectrum.comap_surjective_of_faithfullyFlat, Module.Flat.iff_forall_isTrivialRelation, Module.Flat.projective_of_finitePresentation, LinearMap.tensorKerEquiv, PrimeSpectrum.comap_surjective_iff_injective_of_finite]
  E1: auto
families: []
requires: [V08, V10.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Faithfully flat algebras and flatness criteria

### Overview

Section 1 of this chapter defines flat modules and proves the first criteria. This section collects the library that is built on that definition. A flat module $M$ keeps exact sequences exact under $M \otimes_R -$. A faithfully flat module also reflects exactness: a sequence is exact if and only if it is exact after the tensor product with $M$. Faithfully flat algebras are the base changes along which properties of modules and of ring maps can be checked and then brought back. They are the algebraic form of a covering in algebraic geometry.

The modules of this section give the equivalent forms of faithful flatness, its consequences for ideals and prime spectra, the descent of injectivity and surjectivity, the equational criterion for flatness, the compatibility of flat base change with kernels and equalizers, the local nature of flatness, and the rank of a finite flat algebra. The tensor products are those of Volume 8, and the local rings are those of Chapter 2.

### The library around it

#### Faithfully flat modules

The class `Module.FaithfullyFlat R M` extends `Module.Flat R M` with one field, `Module.FaithfullyFlat.submodule_ne_top`: for each maximal ideal $\mathfrak m$ of $R$, $\mathfrak m M \ne M$. The lemma `Module.faithfullyFlat_iff` states the definition, and `Module.FaithfullyFlat.mk` builds a term from it. The module `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` proves the usual list of equivalent conditions. Each one adds a condition to flatness.

| Lean name | The condition added to flatness |
|---|---|
| `Module.FaithfullyFlat.iff_flat_and_proper_ideal` | $IM \ne M$ for each proper ideal $I$ |
| `Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top` | $IM = M$ implies $I = R$ |
| `Module.FaithfullyFlat.iff_flat_and_rTensor_faithful` | $N \ne 0$ implies $N \otimes_R M \ne 0$ |
| `Module.FaithfullyFlat.iff_flat_and_lTensor_faithful` | $N \ne 0$ implies $M \otimes_R N \ne 0$ |
| `Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality` | $N \otimes_R M = 0$ implies $N = 0$ |
| `Module.FaithfullyFlat.iff_zero_iff_rTensor_zero` | a map $f$ is $0$ if and only if $f \otimes M$ is $0$ |
| `Module.FaithfullyFlat.iff_exact_iff_rTensor_exact` | a sequence is exact if and only if it is exact after $- \otimes_R M$ |

The step from $\mathfrak m M \ne M$ to $IM \ne M$ for a proper ideal $I$ is short: $I$ lies in a maximal ideal $\mathfrak m$, and $IM \subseteq \mathfrak m M \ne M$. The step to the tensor condition uses a cyclic module. If $N \ne 0$, pick $x \ne 0$ in $N$. Then $Rx \cong R/I$ with $I = \operatorname{ann}(x)$ proper, and $R/I \otimes_R M \cong M/IM \ne 0$. Flatness makes $Rx \otimes_R M \to N \otimes_R M$ injective, so $N \otimes_R M \ne 0$.

The consequences for maps come in left and right forms. With $M$ faithfully flat, `Module.FaithfullyFlat.lTensor_injective_iff_injective`, `Module.FaithfullyFlat.lTensor_surjective_iff_surjective` and `Module.FaithfullyFlat.lTensor_bijective_iff_bijective` say that $M \otimes f$ has the property if and only if $f$ has it. The lemmas `Module.FaithfullyFlat.lTensor_reflects_exact` and `Module.FaithfullyFlat.rTensor_reflects_exact` reflect exactness. For an algebra $A$ that is faithfully flat over $R$, the same facts are stated for base change: `LinearMap.baseChange_injective_iff`, `LinearMap.baseChange_surjective_iff`, `LinearMap.baseChange_bijective_iff` and `LinearMap.isUnit_baseChange_iff`. Submodules embed: `Submodule.baseChangeOrderEmbedding` is an order embedding of the submodules of $M$ into those of $A \otimes_R M$, with `Submodule.baseChange_le_iff` and `Submodule.baseChange_inj`. So `Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat` and `Submodule.IsArtinian.of_isArtinian_tensorProduct_of_faithfullyFlat` bring the chain conditions back from $A \otimes_R M$ to $M$, and `Module.Flat.of_flat_tensorProduct` does the same for flatness.

The instances give the first examples. A nontrivial free module is faithfully flat, `Module.FaithfullyFlat.instOfNontrivialOfFree`, and so is $R$ itself, `Module.FaithfullyFlat.self`. Faithful flatness is stable under base change, `Module.FaithfullyFlat.instTensorProduct`, under composition, `Module.FaithfullyFlat.trans`, and under nonempty direct sums, `Module.FaithfullyFlat.directSum`.

#### Faithfully flat algebras

Let $B$ be an $A$-algebra that is faithfully flat as an $A$-module. The module `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra` proves the following.

**The unit map is injective.** For each $A$-module $M$, the map $M \to B \otimes_A M$, $m \mapsto 1 \otimes m$, is injective. This is `Module.FaithfullyFlat.tensorProduct_mk_injective`. Proof sketch: by faithful flatness, it suffices to show that the map stays injective after $B \otimes_A -$. The new map is $B \otimes_A M \to B \otimes_A B \otimes_A M$, $b \otimes m \mapsto b \otimes 1 \otimes m$. The multiplication $B \otimes_A B \to B$ gives a left inverse, so the map is injective. The lemma `Module.FaithfullyFlat.one_tmul_eq_zero_iff` is the same fact for one element.

**Contraction of an extended ideal.** For each ideal $I$ of $A$, $(IB) \cap A = I$, `Ideal.comap_map_eq_self_of_faithfullyFlat`. Apply the previous fact to $M = A/I$: the map $A/I \to B \otimes_A A/I \cong B/IB$ is injective, and its kernel is $(IB \cap A)/I$. So `Ideal.map_injective_of_faithfullyFlat` holds, and `Ideal.comap_surjective_of_faithfullyFlat` says that each ideal of $A$ is a contraction.

**Surjectivity on spectra.** The map $\operatorname{Spec} B \to \operatorname{Spec} A$ is surjective, `PrimeSpectrum.comap_surjective_of_faithfullyFlat`. Proof: let $\mathfrak p$ be a prime of $A$ and $\kappa(\mathfrak p)$ its residue field. The ring $B \otimes_A \kappa(\mathfrak p)$ is nonzero by faithful flatness, so it has a prime ideal. Its contraction to $B$ is a prime $\mathfrak q$, and $\mathfrak q \cap A = \mathfrak p$ because the map factors through $\kappa(\mathfrak p)$. The form with `Ideal.LiesOver` is `Ideal.exists_isPrime_liesOver_of_faithfullyFlat`. The converse holds for flat maps: `Module.FaithfullyFlat.of_comap_surjective` says that a flat algebra with a surjective map on spectra is faithfully flat.

For local rings, `Module.FaithfullyFlat.of_flat_of_isLocalHom` says that a flat local homomorphism of local rings is faithfully flat, and `Module.FaithfullyFlat.isLocalHom` says that the algebra map of a faithfully flat algebra is a local homomorphism. The lemma `Module.FaithfullyFlat.of_isIntegral_of_isDomain` covers a flat integral extension of a domain.

#### Descent of properties of ring maps

The module `Mathlib.RingTheory.Flat.FaithfullyFlat.Descent` proves that injectivity, surjectivity and bijectivity of a ring map $A \to T$ can be checked after a faithfully flat base change $A \to S$. The statements are `Module.FaithfullyFlat.injective_of_tensorProduct`, `Module.FaithfullyFlat.surjective_of_tensorProduct` and `Module.FaithfullyFlat.bijective_of_tensorProduct`: if $S \to S \otimes_A T$ has the property, then $A \to T$ has it. The forms for the framework of ring map properties are `RingHom.FaithfullyFlat.codescendsAlong_injective`, `RingHom.FaithfullyFlat.codescendsAlong_surjective` and `RingHom.FaithfullyFlat.codescendsAlong_bijective`.

#### The equational criterion

A relation $\sum_i f_i x_i = 0$ in $M$, with $f_i \in R$ and $x_i \in M$, is trivial when there are $y_1, \dots, y_k \in M$ and $a_{ij} \in R$ with $x_i = \sum_j a_{ij} y_j$ for each $i$ and $\sum_i f_i a_{ij} = 0$ for each $j$. This is `Module.IsTrivialRelation`. A trivial relation is a relation: $\sum_i f_i x_i = \sum_j \big(\sum_i f_i a_{ij}\big) y_j = 0$, which is `Module.sum_smul_eq_zero_of_isTrivialRelation`. The equational criterion `Module.Flat.iff_forall_isTrivialRelation` says that $M$ is flat if and only if each relation in $M$ is trivial. The list `Module.Flat.tfae_equational_criterion` gives this with the ideal criterion and with the factorization forms.

The factorization form is the most useful. `Module.Flat.iff_forall_exists_factorization` says: $M$ is flat if and only if each map $x : R^l \to M$ that kills an element $f$ factors as $x = y \circ a$ through some $R^k$, with $a(f) = 0$. The lemma `Module.Flat.exists_factorization_of_finitePresentation` extends this to a map from a finitely presented module: each map $P \to M$ factors through a finite free module.

**Theorem.** A flat module $M$ of finite presentation is projective (`Module.Flat.projective_of_finitePresentation`).

*Proof.* Apply the factorization to the identity $M \to M$. It gives $M \xrightarrow{h_2} R^k \xrightarrow{h_3} M$ with $h_3 \circ h_2 = \mathrm{id}$. So $M$ is a direct summand of $R^k$, hence projective. $\square$

#### Flat base change of kernels and equalizers

Let $S$ be an $R$-algebra and $M$ an $S$-module that is flat over $R$. For an $R$-linear map $f : N \to P$, the natural map $M \otimes_R \ker f \to \ker(M \otimes f)$ is an isomorphism, `LinearMap.tensorKerEquiv`. The proof is exactness: $0 \to \ker f \to N \to P$ is exact, and $M \otimes_R -$ keeps it exact. The same holds for the equalizer of two maps $f, g$, `LinearMap.tensorEqLocusEquiv`, since the equalizer is the kernel of $f - g$. For algebra maps $f, g : A \to B$ and a flat $R$-algebra $T$, `AlgHom.tensorEqualizerEquiv` is the isomorphism of algebras $T \otimes_R \operatorname{eq}(f, g) \cong \operatorname{eq}(T \otimes f, T \otimes g)$. The base change form `LinearMap.ker_baseChange` says $\ker(f_S) = (\ker f)_S$ for a flat algebra $S$. The predicate `RingHom.HasStableEqualizers` names the property of a class of ring maps for which this base change of equalizers holds in general.

In the category `ModuleCat R`, flatness is exactness. The lemmas `Module.Flat.iff_lTensor_preserves_shortComplex_exact` and `Module.Flat.iff_rTensor_preserves_shortComplex_exact` say that $M$ is flat if and only if tensoring with $M$ keeps exact short complexes exact, and `Module.Flat.iff_preservesFiniteLimits_tensorLeft` says that it is flat if and only if the functor preserves finite limits.

Two smaller modules belong here. `IsBaseChange.of_left_exact` in `Mathlib.RingTheory.Flat.IsBaseChange` says that a kernel of a base change is the base change of the kernel, for a flat algebra and a map of left exact sequences. Over a domain, `TensorProduct.map_injective_of_flat_flat_of_isDomain` says that $f \otimes g$ is injective when $f$ and $g$ are injective and their sources are flat. Its consequence `LinearIndependent.tmul_of_isDomain` says that the products $v_i \otimes w_j$ of two linearly independent families are linearly independent.

#### Flatness is local

The module `Mathlib.RingTheory.Flat.Localization` proves that flatness can be checked locally. The lemma `Module.flat_of_localized_maximal` says that $M$ is flat if $M_{\mathfrak m}$ is flat for each maximal ideal $\mathfrak m$, and `Module.flat_of_localized_span` checks it on the localizations $M_{s}$ for a family $s$ that generates the unit ideal. The forms `Module.flat_of_isLocalized_maximal` and `Module.flat_of_isLocalized_span` take any localization in the sense of `IsLocalizedModule`. For an $S$-module $M$ with $S$ a localization of $R$, `Module.flat_iff_of_isLocalization` says that $M$ is flat over $S$ if and only if it is flat over $R$. A localization of a flat algebra is flat, `Localization.flat`, and `IsSMulRegular.of_isLocalization` says that a regular element stays regular in a localization.

#### Finite flat algebras and rank

Let $S$ be a finite flat $R$-algebra. For a prime $\mathfrak p$ of $R$, the number `Module.rankAtStalk S p` is the rank of the localization $S_{\mathfrak p}$ over the local ring $R_{\mathfrak p}$. The module `Mathlib.RingTheory.Flat.Rank` relates this rank to the map $R \to S$.

| Lean name | Statement |
|---|---|
| `PrimeSpectrum.rankAtStalk_pos_iff_mem_range_comap` | $\operatorname{rank}_{\mathfrak p} S > 0$ if and only if $\mathfrak p$ is in the image of $\operatorname{Spec} S$ |
| `PrimeSpectrum.comap_surjective_iff_injective_of_finite` | $\operatorname{Spec} S \to \operatorname{Spec} R$ is surjective if and only if $R \to S$ is injective |
| `Module.rankAtStalk_le_one_iff_surjective` | the rank is at most $1$ at each prime if and only if $R \to S$ is surjective |
| `Module.algebraMap_bijective_iff_rankAtStalk` | the rank is $1$ at each prime if and only if $R \to S$ is bijective |
| `Module.Flat.tfae_algebraMap_surjective` | $R \to S$ is surjective if and only if the multiplication $S \otimes_R S \to S$ is bijective |
| `RingHom.finrank` | the rank function of a finite flat ring map |

The first line is the key one. The fiber $S \otimes_R \kappa(\mathfrak p)$ is a vector space over $\kappa(\mathfrak p)$ of the same dimension as the rank, because $S_{\mathfrak p}$ is free over $R_{\mathfrak p}$, and the fiber is nonzero if and only if some prime of $S$ lies over $\mathfrak p$. The module `Mathlib.RingTheory.Flat.LocallyFree` adds two results: `Module.bijective_of_surjective_of_rankAtStalk_eq` says that a surjection of finite flat modules with the same rank at each maximal ideal is bijective, and `Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant` gives a free localization $M_a$ near a prime when the rank is constant.

#### Common errors

1. `Module.FaithfullyFlat` needs a ring and an additive group, not a semiring. The lemmas about algebras ask for `[Module.FaithfullyFlat A B]`; there is no separate class for algebras.
2. The two directions of a tensor product have separate names. For example, `Module.FaithfullyFlat.lTensor_reflects_exact` is about $M \otimes_R -$, and `Module.FaithfullyFlat.rTensor_reflects_exact` is about $- \otimes_R M$. Choose the one that matches the goal, or rewrite with `TensorProduct.comm`.
3. `Module.IsTrivialRelation` uses a `Fintype` index type. The criterion `Module.Flat.iff_forall_isTrivialRelation` is stated for `Fin l`, so a relation over another finite type must first be reindexed, with `Equiv.isTrivialRelation_comp`.

### Exercises

1. (A) Show that $\mathbb{Q}$ is flat but not faithfully flat over $\mathbb{Z}$, with the condition $p\mathbb{Q} = \mathbb{Q}$.
2. (A) Show that $R[X]$ is faithfully flat over $R$, with `Module.FaithfullyFlat.instOfNontrivialOfFree`.
3. (B) Let $B$ be faithfully flat over $A$. Show that $A$ is Noetherian when $B$ is Noetherian, with `Ideal.map_injective_of_faithfullyFlat`.
4. (B) Show that a finite flat algebra $S \ne 0$ over a local ring $R$ is faithfully flat, with the rank at the maximal ideal.
5. (B) Write the relation $2 \cdot 3 - 3 \cdot 2 = 0$ in the $\mathbb{Z}$-module $\mathbb{Z}$ as a trivial relation.
6. (C) Show that $\prod_{\mathfrak m} R_{\mathfrak m}$, over all maximal ideals, is faithfully flat over $R$ when $R$ has finitely many maximal ideals.

### Reference

<?reference?>
