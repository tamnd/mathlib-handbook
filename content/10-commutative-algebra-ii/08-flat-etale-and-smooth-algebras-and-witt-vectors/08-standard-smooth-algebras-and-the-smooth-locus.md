---
title: Standard smooth algebras and the smooth locus
kind: api
modules:
  - Mathlib.RingTheory.Smooth.StandardSmooth
  - Mathlib.RingTheory.Smooth.StandardSmoothCotangent
  - Mathlib.RingTheory.Smooth.StandardSmoothOfFree
  - Mathlib.RingTheory.Smooth.Locus
  - Mathlib.RingTheory.Smooth.Kaehler
  - Mathlib.RingTheory.Smooth.Local
  - Mathlib.RingTheory.Smooth.Fiber
  - Mathlib.RingTheory.Smooth.Field
  - Mathlib.RingTheory.Smooth.Pi
  - Mathlib.RingTheory.Smooth.Quotient
  - Mathlib.RingTheory.Smooth.AdicCompletion
  - Mathlib.RingTheory.Smooth.IntegralClosure
  - Mathlib.RingTheory.Smooth.NoetherianDescent
explains:
  E2: [Algebra.IsStandardSmooth, Algebra.IsStandardSmoothOfRelativeDimension, Algebra.SubmersivePresentation.basisKaehler, Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential, Algebra.Smooth.exists_span_eq_top_isStandardSmooth, Algebra.smoothLocus, Algebra.smoothLocus_eq_compl_support_inter, retractionKerToTensorEquivSection, Algebra.Smooth.of_formallySmooth_fiber, TensorProduct.toIntegralClosure_bijective_of_smooth]
  E1: auto
families: []
requires: [V10.C02, V10.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Standard smooth algebras and the smooth locus

### Overview

Section 2 defines a smooth algebra by the infinitesimal lifting property. This definition is abstract. A concrete model is a standard smooth algebra: a quotient $R[x_1, \dots, x_n]/(f_1, \dots, f_c)$ for which the Jacobian determinant of $f_1, \dots, f_c$ in the last $c$ variables is a unit. The geometric picture is a smooth variety cut out by $c$ equations, of dimension $n - c$. The main theorem says that every smooth algebra is locally standard smooth.

This section describes standard smooth algebras and their relative dimension, the basis of Kähler differentials that a submersive presentation gives, the local structure theorem, the smooth locus, the description of smoothness by sections and retractions, the fiber criterion, smoothness over fields, and some closure properties.

### The library around it

#### Standard smooth algebras

The class `Algebra.IsStandardSmooth R S` in `Mathlib.RingTheory.Smooth.StandardSmooth` says that $S$ has a submersive presentation with finitely many generators and relations. A submersive presentation is the structure `Algebra.SubmersivePresentation` of Section 7: the relations are indexed by a subset of the generators, and the Jacobian `Algebra.PreSubmersivePresentation.jacobian` is a unit in $S$. The class `Algebra.IsStandardSmoothOfRelativeDimension n R S` adds that the number of generators minus the number of relations is $n$.

| Lean name | Statement |
|---|---|
| `Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial` | $R[x_1, \dots, x_n]$ is standard smooth of relative dimension $n$ |
| `Algebra.IsStandardSmoothOfRelativeDimension.localization_away` | $R_r$ is standard smooth of relative dimension $0$ |
| `Algebra.IsStandardSmoothOfRelativeDimension.trans` | relative dimensions add in a tower |
| `Algebra.IsStandardSmoothOfRelativeDimension.baseChange` | standard smoothness is stable under base change |
| `Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv` | it is invariant under isomorphism |
| `Algebra.IsStandardSmooth.trans` | the same composition law without the dimension |
| `Algebra.IsStandardSmooth.relativeDimension` | the relative dimension of a standard smooth algebra |

The relative dimension is well defined, since it is the rank of $\Omega_{S/R}$. The module `Mathlib.RingTheory.Smooth.StandardSmoothCotangent` proves this.

#### Differentials of a submersive presentation

Let $P$ be a submersive presentation of $S$ with generators $x_i$ for $i \in \iota$ and relations $f_j$ for $j \in \sigma$, with $\sigma \subseteq \iota$. The cotangent space $I/I^2$ of the presentation is free with basis the classes of the relations, `Algebra.SubmersivePresentation.basisCotangent`, and `Algebra.SubmersivePresentation.cotangentEquiv` identifies it with $S^\sigma$. The naive cotangent complex $I/I^2 \to S \otimes \Omega_{P/R}$ of Section 6 is injective, `Algebra.SubmersivePresentation.cotangentComplex_injective`, since its matrix contains the invertible Jacobian.

**Theorem.** The module $\Omega_{S/R}$ is free with basis $dx_i$ for $i \in \iota \setminus \sigma$. So its rank is the relative dimension. These are `Algebra.SubmersivePresentation.basisKaehler`, `Algebra.SubmersivePresentation.free_kaehlerDifferential` and `Algebra.SubmersivePresentation.rank_kaehlerDifferential`.

*Proof sketch.* The cotangent sequence $0 \to I/I^2 \to \bigoplus_{i \in \iota} S\,dx_i \to \Omega_{S/R} \to 0$ is exact. The map sends the class of $f_j$ to $\sum_i (\partial f_j / \partial x_i)\,dx_i$. The square block of this matrix on $\sigma$ is the Jacobian, which is invertible. So the images of the $f_j$ and the $dx_i$ for $i \notin \sigma$ form a basis of the middle term. The quotient is free on the $dx_i$ with $i \notin \sigma$. $\square$

For a class form, `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential` says that the rank is $n$. The instance `Algebra.instSmoothOfIsStandardSmooth` says that a standard smooth algebra is smooth.

#### Smooth is locally standard smooth

The module `Mathlib.RingTheory.Smooth.StandardSmoothOfFree` proves the converse in a local form.

**Theorem.** Let $S$ be a finitely presented $R$-algebra. Then $S$ is standard smooth if and only if $H_1(L_{S/R}) = 0$ and $\Omega_{S/R}$ has a basis of differentials $ds_i$. This is `Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential`.

*Proof sketch.* For a standard smooth algebra the two conditions follow from the theorem above. For the converse, choose a presentation $R[x_1, \dots, x_n] \to S$ whose first generators map to the $s_i$ of the basis. Since $H_1 = 0$, the sequence $0 \to I/I^2 \to S^n \to \Omega_{S/R} \to 0$ is exact and splits. So $I/I^2$ is free, and after adding generators its basis comes from relations whose Jacobian in the remaining variables is invertible. $\square$

Then `Algebra.Smooth.exists_span_eq_top_isStandardSmooth` says that a smooth algebra $S$ has elements $f_1, \dots, f_k$ that generate the unit ideal with each $S_{f_i}$ standard smooth over $R$. The pointwise form is `Algebra.IsSmoothAt.exists_notMem_isStandardSmooth`. In relative dimension zero, `Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero` says that étale is the same as standard smooth of relative dimension $0$.

#### The smooth locus

The module `Mathlib.RingTheory.Smooth.Locus` defines `Algebra.smoothLocus R A`, the set of primes $\mathfrak p$ of $A$ with $A_{\mathfrak p}$ formally smooth over $R$. The predicate `Algebra.IsSmoothAt R p` says that $\mathfrak p$ is in the locus.

1. `Algebra.smoothLocus_eq_compl_support_inter`: for an essentially finite type algebra, the locus is the set of primes outside the support of $H_1(L_{A/R})$ at which $\Omega_{A/R}$ is free.
2. `Algebra.isOpen_smoothLocus`: for a finitely presented algebra the locus is open.
3. `Algebra.smoothLocus_eq_univ_iff`: the locus is the whole spectrum if and only if $A$ is formally smooth.
4. `Algebra.basicOpen_subset_smoothLocus_iff`: $D(f)$ is in the locus if and only if $A_f$ is formally smooth.
5. `Algebra.IsSmoothAt.exists_notMem_smooth`: a smooth point has a neighborhood $D(f)$ with $A_f$ smooth.

The free locus of a module is in Chapter 12. The étale locus of Section 5 is the intersection of the smooth locus with the unramified locus.

#### Sections, retractions and the local criterion

Let $P \to S$ be surjective with kernel $I$ and $I^2 = 0$. The module `Mathlib.RingTheory.Smooth.Kaehler` relates algebra sections $S \to P$ to linear retractions of the map $I \to S \otimes_P \Omega_{P/R}$. The equivalence `retractionKerToTensorEquivSection` is this bijection, and `retractionKerCotangentToTensorEquivSection` is the form for $P \to P/I^2 \to S$ without the hypothesis $I^2 = 0$. The isomorphism `tensorKaehlerQuotKerSqEquiv` says that $S \otimes \Omega_{(P/I^2)/R} \cong S \otimes \Omega_{P/R}$. So a smooth $S$ is the same as a split injective naive cotangent complex, and this is the form of `Algebra.FormallySmooth.iff_split_injection`.

Over a local ring the splitting can be tested on the residue field. Let $S$ be local with residue field $k$, and let $P \to S$ be a surjection from a formally smooth $R$-algebra with $\Omega_{P/R}$ free and finite and with finitely generated kernel. Then `Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField` in `Mathlib.RingTheory.Smooth.Local` says that $S$ is formally smooth if and only if the complex stays injective after $k \otimes_S -$. The proof is Nakayama's lemma of Chapter 2. The form for an extension is `Algebra.FormallySmooth.iff_injective_lTensor_residueField`.

#### The fiber criterion

**Theorem.** A flat and finitely presented algebra $S$ over $R$ is smooth if each fiber $\kappa(\mathfrak p) \otimes_R S$ is formally smooth over $\kappa(\mathfrak p)$. This is `Algebra.Smooth.of_formallySmooth_fiber` in `Mathlib.RingTheory.Smooth.Fiber`.

*Proof sketch.* Reduce to local rings. The local criterion tests injectivity of the cotangent complex after tensor with the residue field of $S$. This residue field is also the residue field of the fiber. On the fiber the complex is injective, since the fiber is smooth. Flatness of $S$ says that the complex of $S$ and the complex of the fiber agree after this tensor product. $\square$

The pointwise form is `Algebra.IsSmoothAt.of_formallySmooth_fiber`, and the local form is `Algebra.FormallySmooth.of_formallySmooth_residueField_tensor`. The same module proves `Algebra.Etale.of_formallyUnramified_of_flat`: a flat, finitely presented and unramified algebra is étale, and `Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat` is the pointwise form.

#### Fields, products and quotients

1. `Algebra.FormallySmooth.of_perfectField` in `Mathlib.RingTheory.Smooth.Field`: an essentially finite type field extension of a perfect field is formally smooth.
2. `Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable`: $L/K$ is formally smooth when it is separable over a purely transcendental subextension $K(v)$. The case $L = K(v)$ is `Algebra.FormallySmooth.of_algebraicIndependent`.
3. `Algebra.FormallySmooth.pi_iff` in `Mathlib.RingTheory.Smooth.Pi`: a finite product is formally smooth if and only if each factor is, and `Algebra.FormallySmooth.of_pi` gives one factor.
4. `Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_flat` in `Mathlib.RingTheory.Smooth.Quotient`: for a flat $S$ over $R$ and a square zero ideal $J$ of $R$, if $S/JS$ is formally smooth over $R/J$ then $S$ is formally smooth over $R$. The ring hom form is `RingHom.FormallySmooth.of_flat_of_ker_eq_map_of_square_zero`.
5. `Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete` in `Mathlib.RingTheory.Smooth.AdicCompletion`: the lifting property extends from square zero ideals to an ideal $I$ for which $S$ is $I$-adically complete. The lift is built step by step through $S/I^n$, as in Chapter 6.

#### Integral closure and Noetherian descent

The map `TensorProduct.toIntegralClosure R S B` in `Mathlib.RingTheory.Smooth.IntegralClosure` sends $S \otimes_R \overline{R}^B$ to the integral closure of $S$ in $S \otimes_R B$. It is injective for a flat $S$, `TensorProduct.toIntegralClosure_injective_of_flat`. The theorem `TensorProduct.toIntegralClosure_bijective_of_smooth` says that it is bijective for a smooth $S$: smooth base change commutes with integral closure. The proof reduces to standard étale algebras and to polynomial rings, `TensorProduct.toIntegralClosure_bijective_of_isLocalizationAway` and `TensorProduct.toIntegralClosure_mvPolynomial_bijective`.

The module `Mathlib.RingTheory.Smooth.NoetherianDescent` proves that a smooth algebra comes from a smooth algebra over a Noetherian base. By `Algebra.Smooth.exists_finiteType`, a smooth $A$-algebra $B$ is $A \otimes_{A_0} B_0$ for a subring $A_0$ of finite type over $R$ and a smooth $A_0$-algebra $B_0$. The form `Algebra.Smooth.exists_subalgebra_fg` takes $A_0$ inside $A$.

#### Common errors

1. `Algebra.IsStandardSmooth R S` is a property of $S$, not a choice of presentation. To compute with the Jacobian, take the presentation from `Algebra.IsStandardSmooth.out`.
2. `Algebra.smoothLocus R A` uses formal smoothness of the local rings. Openness and the link with smoothness of $A_f$ need `Algebra.FinitePresentation R A`.
3. `Algebra.Smooth.of_formallySmooth_fiber` needs `Module.Flat R S`. The algebra $\mathbb{Z}/p$ over $\mathbb{Z}$ has smooth fibers but is not smooth.

### Exercises

1. (A) Show that $R[x, y]/(y - x^2)$ is standard smooth of relative dimension $1$ over $R$, and find a basis of its Kähler differentials.
2. (A) Use `Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero` to show that $R[x]_{f'}/(f)$ is étale over $R$ for a monic $f$.
3. (B) Let $k$ be a field and $S = k[x, y]/(y^2 - x^3)$. Compute $\Omega_{S/k}$ and show that the smooth locus is the complement of the origin.
4. (B) Show that $\mathbb{F}_p(t^{1/p})$ is not formally smooth over $\mathbb{F}_p(t)$, and explain why this does not contradict `Algebra.FormallySmooth.of_perfectField`.
5. (B) Prove that a standard smooth algebra of relative dimension $n$ has $\Omega_{S/R}$ of rank $n$, from the cotangent sequence.
6. (C) Show that $R \to R[x, y]/(xy - r)$ is smooth at the primes that do not contain $(x, y)$, and that it is flat. For which $r$ is it smooth?

### Reference

<?reference?>
