---
title: Algebras of finite type and finite presentation
kind: api
modules:
  - Mathlib.RingTheory.FiniteType
  - Mathlib.RingTheory.FinitePresentation
  - Mathlib.RingTheory.FiniteStability
  - Mathlib.RingTheory.EssentialFiniteness
  - Mathlib.RingTheory.Finiteness.FiniteTypeLocal
  - Mathlib.RingTheory.Finiteness.FinitePresentationLocal
explains:
  E2: [Algebra.FiniteType, Algebra.FinitePresentation, Algebra.FinitePresentation.of_finiteType, Algebra.FiniteType.isNoetherianRing, Algebra.FinitePresentation.ker_fG_of_surjective, Algebra.EssFiniteType, MonoidAlgebra.finiteType_iff_fg, Algebra.FiniteType.of_span_eq_top_target]
  E1: auto
families: []
requires: [V08, V09]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Algebras of finite type and finite presentation

### Overview

An $R$-algebra $S$ is of finite type when finitely many elements generate it as an algebra. Then $S$ is a quotient of a polynomial ring $R[X_1, \dots, X_n]$. The algebra is finitely presented when, in addition, the kernel of such a surjection is a finitely generated ideal. These two conditions are the algebraic form of "a variety cut out by finitely many equations", and they are the hypotheses of the Nullstellensatz, of the theory of étale and smooth algebras in Chapter 8, and of many local properties in Chapter 12.

This section covers the definitions, the comparison with the finite modules of Section 1, the stability under composition, quotients and base change, and the essentially finite type algebras, which are localizations of algebras of finite type. It ends with the local results: an algebra is of finite type, or finitely presented, when it is so on an open cover of its spectrum.

### The library around it

#### Algebras of finite type

The module `Mathlib.RingTheory.FiniteType` defines the class `Algebra.FiniteType R S`: the top subalgebra of $S$ is finitely generated, that is, $S = R[s_1, \dots, s_n]$ for some $s_i \in S$. The main characterization is `Algebra.FiniteType.iff_quotient_mvPolynomial''`: $S$ is of finite type if and only if there is $n$ and a surjective $R$-algebra map from `MvPolynomial (Fin n) R` onto $S$. The map sends $X_i$ to $s_i$. For noncommutative algebras, `Algebra.FiniteType.iff_quotient_freeAlgebra` uses the free algebra in place of the polynomial ring.

A finite module is an algebra of finite type: module generators also generate the algebra. This is `Module.Finite.finiteType`. The converse fails, since $R[X]$ is of finite type but not a finite $R$-module.

| Lean name | Statement |
|---|---|
| `Algebra.FiniteType.instPolynomial` | $R[X]$ is of finite type over $R$ |
| `Algebra.FiniteType.instMvPolynomialOfFinite` | $R[X_i : i \in \iota]$ is of finite type for $\iota$ finite |
| `Algebra.FiniteType.of_surjective` | the image of an algebra of finite type is of finite type |
| `Algebra.FiniteType.quotient` | $S/I$ is of finite type when $S$ is |
| `Algebra.FiniteType.equiv` | the property is invariant under algebra isomorphisms |
| `Algebra.FiniteType.trans` | in a tower $R \to S \to A$, finite type over finite type is finite type |
| `Algebra.FiniteType.of_restrictScalars_finiteType` | if $A$ is of finite type over $R$, then it is of finite type over $S$ |
| `Algebra.FiniteType.prod` | $S \times T$ is of finite type when $S$ and $T$ are |
| `Subalgebra.fg_iff_finiteType` | a subalgebra is finitely generated if and only if it is of finite type as an algebra |

The ring map form is `RingHom.FiniteType`, with `RingHom.FiniteType.comp` for composites and `RingHom.Finite.finiteType` for the passage from finite maps. The algebra map form is `AlgHom.FiniteType`.

**Proof of `Algebra.FiniteType.trans`.** Let $S = R[s_1, \dots, s_m]$ and $A = S[a_1, \dots, a_n]$. The $R$-subalgebra $B = R[s_1, \dots, s_m, a_1, \dots, a_n]$ of $A$ contains the image of $S$ and all the $a_j$. Every element of $A$ is a polynomial in the $a_j$ with coefficients in $S$, so it is in $B$. Thus $A = B$ is of finite type over $R$. $\square$

#### Noetherian rings and monoid algebras

The Hilbert basis theorem of Volume 9 gives `Algebra.FiniteType.isNoetherianRing`: an algebra of finite type over a Noetherian ring is a Noetherian ring. The proof is two steps. `MvPolynomial (Fin n) R` is Noetherian by the basis theorem, and a quotient of a Noetherian ring is Noetherian.

For a monoid $M$, the lemma `MonoidAlgebra.finiteType_iff_fg` says that the monoid algebra $R[M]$ is of finite type if and only if $M$ is a finitely generated monoid, for a nontrivial ring $R$. The additive form is `AddMonoidAlgebra.finiteType_iff_fg`, and `MonoidAlgebra.finiteType_iff_group_fg` is the form for groups. One direction is clear: generators $m_1, \dots, m_k$ of $M$ give the algebra generators $m_1, \dots, m_k$ of $R[M]$. For the other direction, a finite set of algebra generators involves finitely many elements of $M$ in their supports, and these elements generate $M$.

The same module has the instance `CommRing.orzechProperty`: every commutative ring has the Orzech property. For a finite module $M$ and a submodule $N$, a surjective linear map $N \to M$ is injective. In particular, a surjective endomorphism of a finite module is injective.

#### Finitely presented algebras

The module `Mathlib.RingTheory.FinitePresentation` defines the class `Algebra.FinitePresentation R A`. The definition asks for $n$ and a surjection $f$ from `MvPolynomial (Fin n) R` onto $A$ whose kernel is a finitely generated ideal. The lemma `Algebra.FinitePresentation.iff` states this as an isomorphism of $A$ with a quotient $R[X_1, \dots, X_n]/I$ for a finitely generated ideal $I$. A finitely presented algebra is of finite type, `Algebra.FiniteType.of_finitePresentation`.

Over a Noetherian ring the two conditions are the same, `Algebra.FinitePresentation.of_finiteType`. The reason: the polynomial ring is Noetherian, so every kernel is finitely generated. Without the Noetherian hypothesis, the quotient $R/I$ is of finite type for every ideal $I$, but it is finitely presented only when $I$ is finitely generated.

The choice of generators does not matter. This is `Algebra.FinitePresentation.ker_fG_of_surjective`: if $A$ and $B$ are finitely presented and $f : A \to B$ is a surjective algebra map, then the kernel of $f$ is finitely generated. So every presentation of a finitely presented algebra by finitely many generators has finitely many relations.

**Proof sketch of `Algebra.FinitePresentation.ker_fG_of_surjective`.** Take a presentation $R[X_1, \dots, X_n] \to A$ with kernel $(g_1, \dots, g_k)$, and a presentation $R[Y_1, \dots, Y_m] \to B$ with kernel $(h_1, \dots, h_l)$. Choose polynomials $p_j$ in the $X_i$ that map to the images of the $Y_j$ in $B$, and polynomials $q_i$ in the $Y_j$ that map to $f(x_i)$. The kernel of $R[X] \to B$ is then generated by the $g$'s, the $h$'s with $Y_j$ replaced by $p_j$, and the elements $X_i - q_i(p)$. These are finitely many, and their images in $A$ generate the kernel of $f$. $\square$

| Lean name | Statement |
|---|---|
| `Algebra.FinitePresentation.polynomial` | $R[X]$ is finitely presented |
| `Algebra.FinitePresentation.mvPolynomial` | $R[X_i : i \in \iota]$ is finitely presented for $\iota$ finite |
| `Algebra.FinitePresentation.quotient` | $A/I$ is finitely presented when $A$ is and $I$ is finitely generated |
| `Algebra.FinitePresentation.of_surjective` | if $A$ is finitely presented and $A \to B$ is surjective with a finitely generated kernel, then $B$ is finitely presented |
| `Algebra.FinitePresentation.equiv` | the property is invariant under algebra isomorphisms |
| `Algebra.FinitePresentation.trans` | finitely presented over finitely presented is finitely presented |
| `Algebra.FinitePresentation.of_restrict_scalars_finitePresentation` | if $A$ is finitely presented over $R$ and $S$ is of finite type over $R$, then $A$ is finitely presented over $S$ |

The ring map forms are `RingHom.FinitePresentation` and `AlgHom.FinitePresentation`. The lemma `RingHom.FinitePresentation.of_comp_finiteType` says: if $g \circ f$ is finitely presented and $f$ is of finite type, then $g$ is finitely presented. The induction principle `RingHom.FinitePresentation.polynomial_induction` reduces a property of finitely presented maps to polynomial rings in one variable, quotients by one element, and isomorphisms.

#### Base change

The module `Mathlib.RingTheory.FiniteStability` proves that the two properties are stable under base change. For $R$-algebras $A$ and $B$, the instances `Algebra.FiniteType.baseChange` and `Algebra.FinitePresentation.baseChange` give that $B \otimes_R A$ is of finite type, or finitely presented, over $B$ when $A$ is so over $R$. The proof is the isomorphism $B \otimes_R R[X_1, \dots, X_n]/I \cong B[X_1, \dots, X_n]/IB[X_1, \dots, X_n]$, and $IB[X]$ is finitely generated when $I$ is.

#### Essentially of finite type

The module `Mathlib.RingTheory.EssentialFiniteness` defines `Algebra.EssFiniteType R S`: there is a finite set $\sigma \subseteq S$ such that $S$ is a localization of the subalgebra $R[\sigma]$ at the units of $S$ that lie in it. The unfolded statement is `Algebra.essFiniteType_iff`. A local ring of a variety at a point is the main example: it is a localization of an algebra of finite type, but it is not of finite type.

| Lean name | Statement |
|---|---|
| `Algebra.EssFiniteType.of_finiteType` | an algebra of finite type is essentially of finite type |
| `Algebra.instEssFiniteTypeLocalization` | a localization $S_M$ is essentially of finite type over $S$ |
| `Algebra.EssFiniteType.of_isLocalization` | the same for any type with an `IsLocalization` instance |
| `Algebra.instEssFiniteTypeQuotientIdeal` | a quotient is essentially of finite type |
| `Algebra.EssFiniteType.comp` | the property is stable under composition |
| `Algebra.EssFiniteType.of_comp` | if $T$ is essentially of finite type over $R$, then it is so over $S$ |
| `Algebra.EssFiniteType.baseChange` | the property is stable under base change |
| `Algebra.EssFiniteType.algHom_ext` | two algebra maps out of $S$ that agree on the finite set $\sigma$ are equal |

The last result is the reason for the definition in some proofs: an essentially finite type algebra is determined by a finite amount of data. The chosen finite set is `Algebra.EssFiniteType.finset`, and its subalgebra is `Algebra.EssFiniteType.subalgebra`. The ring map form is `RingHom.EssFiniteType`.

#### Local on the target

The modules `Mathlib.RingTheory.Finiteness.FiniteTypeLocal` and `Mathlib.RingTheory.Finiteness.FinitePresentationLocal` prove that the two properties are local on the spectrum of the target. Let $s \subseteq S$ be a finite set that generates the unit ideal. Then `Algebra.FiniteType.of_span_eq_top_target` says that $S$ is of finite type over $R$ when each localization $S_x$ for $x \in s$ is of finite type over $R$. The finitely presented form is `Algebra.FinitePresentation.of_span_eq_top_target`.

**Proof sketch for finite type.** For each $x \in s$, choose finitely many generators of $S_x$ and write each as $y/x^k$ with $y \in S$. Let $B \subseteq S$ be the subalgebra generated by all these numerators, by the elements of $s$ and by coefficients $c_x$ with $\sum_x c_xx = 1$. For $t \in S$ and $x \in s$, the image of $t$ in $S_x$ is a polynomial in the generators, so $x^{N}t \in B$ for a large $N$. This is `IsLocalization.exists_smul_mem_of_mem_adjoin`. The $x^N$ for $x \in s$ also generate the unit ideal of $B$, so $t = \sum_x d_xx^Nt \in B$. Thus $S = B$. $\square$

The version for the source is `Algebra.FiniteType.of_span_eq_top_source`. The module for finite presentation also has the instance `Algebra.FinitePresentation.pi`: a finite product of finitely presented algebras is finitely presented.

#### Common errors

1. `Algebra.FiniteType` and `Module.Finite` are different classes. A polynomial ring is of finite type and not finite. Use `Module.Finite.finiteType` to pass from the second to the first.
2. `Algebra.FinitePresentation.of_finiteType` is an equivalence that needs `IsNoetherianRing R`. Without it, the conclusion fails for quotients by ideals that are not finitely generated.
3. Base change results are instances on `TensorProduct`. The algebra structure is on $B \otimes_R A$ over $B$, so state the goal over the left factor, or the instance search fails.

### Exercises

1. (A) Show that $\mathbb{Z}[1/2]$ is of finite type over $\mathbb{Z}$ but not a finite $\mathbb{Z}$-module.
2. (A) Show that $\mathbb{Q}$ is essentially of finite type over $\mathbb{Z}$, and that it is not of finite type.
3. (B) Let $R = k[X_1, X_2, \dots]$ and $I = (X_1, X_2, \dots)$. Show that $R/I$ is of finite type over $R$ but not finitely presented over $R$.
4. (B) Prove `Algebra.FiniteType.isNoetherianRing` from `Algebra.FiniteType.iff_quotient_mvPolynomial''` and the Hilbert basis theorem.
5. (B) Use `MonoidAlgebra.finiteType_iff_fg` to show that $k[\mathbb{Q}_{\ge 0}]$ is not of finite type over a field $k$.
6. (C) Let $S$ be an $R$-algebra and let $f, g \in S$ with $(f, g) = S$. Assume that $S_f$ and $S_g$ are finitely presented over $R$. Follow the proof of `Algebra.FiniteType.of_span_eq_top_target` and explain which extra relations a presentation of $S$ needs.

### Reference

<?reference?>
