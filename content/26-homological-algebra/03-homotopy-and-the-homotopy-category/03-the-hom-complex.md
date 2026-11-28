---
title: The Hom complex
kind: api
modules:
  - Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
  - Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
  - Mathlib.Algebra.Homology.HomotopyCategory.HomComplexInduction
  - Mathlib.Algebra.Homology.HomotopyCategory.HomComplexIsStrictlyGE
  - Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
  - Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
explains:
  E2: [CochainComplex.HomComplex.Cochain, CochainComplex.HomComplex.δ, CochainComplex.HomComplex.Cochain.comp, CochainComplex.HomComplex.Cocycle, CochainComplex.HomComplex.Cochain.equivHomotopy, CochainComplex.HomComplex.CohomologyClass, CochainComplex.HomComplex.CohomologyClass.toHom_bijective, CochainComplex.HomComplex.Cochain.rightShift, CochainComplex.HomComplex.Cocycle.equivHomShift, CochainComplex.HomComplex.Cochain.fromSingleEquiv]
  E1: auto
families: []
requires: [V24.C08, V25.C05, V26.C01, V26.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Hom complex

### Overview

For two cochain complexes $K$ and $L$ on $\mathbb{Z}$ in a preadditive category, the Hom complex $\mathrm{Hom}^\bullet(K, L)$ has in degree $n$ the group
$$\mathrm{Hom}^n(K, L) = \prod_{p + n = q} \mathrm{Hom}(K^p, L^q),$$
with the differential $\delta z = d_L \circ z + (-1)^{n+1} z \circ d_K$. Its $0$-cocycles are the morphisms of complexes, its $0$-coboundaries are the null homotopic morphisms, and its $n$-th cohomology is the group of morphisms $K \to L[n]$ in the homotopy category. Section 2 uses the elements of this complex, the cochains, to write the maps of the mapping cone and to prove that the homotopy category is triangulated.

The modules of this section give the cochains and their composition, the differential and its sign rules, the cocycles and the cohomology classes, the behavior under shifts, and the cochains from and to single complexes. A small module constructs a cochain by induction on the degree, and another one gives a vanishing result for bounded complexes.

Throughout, $K$, $L$, $F$, $G$ are cochain complexes on $\mathbb{Z}$ in a preadditive category $C$. All names below are in the namespace `CochainComplex.HomComplex` and are written in full.

### The library around it

#### Cochains and composition

A cochain of degree $n$, an element of `CochainComplex.HomComplex.Cochain` for $F$, $G$ and $n$, is a family of maps $F^p \to G^q$ for all $p$, $q$ with $p + n = q$. It is defined as the family over the type `CochainComplex.HomComplex.Triplet`, which holds two integers and the equation. The basic API:

| Lean name | Statement |
|---|---|
| `CochainComplex.HomComplex.Cochain.mk` | a cochain from a family of maps indexed by $p$, $q$ and a proof of $p + n = q$ |
| `CochainComplex.HomComplex.Cochain.v` | the component $F^p \to G^q$ of a cochain |
| `CochainComplex.HomComplex.Cochain.ext` | two cochains are equal if their components are equal |
| `CochainComplex.HomComplex.Cochain.ofHom` | the $0$-cochain of a morphism of complexes |
| `CochainComplex.HomComplex.Cochain.ofHoms` | the $0$-cochain of any family of maps $F^p \to G^p$ |
| `CochainComplex.HomComplex.Cochain.single` | the cochain with one nonzero component |
| `CochainComplex.HomComplex.Cochain.diff` | the differential of $K$ as a $1$-cochain from $K$ to $K$ |
| `CochainComplex.HomComplex.Cochain.map` | the image of a cochain under an additive functor |

The cochains of each degree form an abelian group, and a module over $R$ when $C$ is $R$-linear. The composition `CochainComplex.HomComplex.Cochain.comp` takes a cochain of degree $n_1$, a cochain of degree $n_2$ and a proof of $n_1 + n_2 = n_{12}$. The degree is part of the data, so the proof argument makes the result type correct without a cast. The formula for components is `CochainComplex.HomComplex.Cochain.comp_v`, and the composition is additive and associative. For associativity with a $0$-cochain in a position, the lemmas `CochainComplex.HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain` and `CochainComplex.HomComplex.Cochain.comp_assoc_of_third_is_zero_cochain` need fewer degree equations than the general one.

#### The differential and cocycles

The differential `CochainComplex.HomComplex.δ` takes two integers $n$, $m$ and a cochain of degree $n$, and gives a cochain of degree $m$. It is zero if $n + 1 \ne m$, by `CochainComplex.HomComplex.δ_shape`. The component formula `CochainComplex.HomComplex.δ_v` reads
$$(\delta z)_{p,q} = z_{p,q-1} \circ d_G + (-1)^m\, d_F \circ z_{p+1,q},$$
with composition written in diagrammatic order as in Mathlib. The main lemmas are:

| Lean name | Statement |
|---|---|
| `CochainComplex.HomComplex.δ_δ` | $\delta \circ \delta = 0$ |
| `CochainComplex.HomComplex.δ_comp` | the Leibniz rule $\delta(z_1 z_2) = z_1\, \delta z_2 + (-1)^{n_2} (\delta z_1) z_2$ |
| `CochainComplex.HomComplex.δ_ofHom` | the cochain of a morphism of complexes is a cocycle |
| `CochainComplex.HomComplex.δ_neg_one_cochain` | the differential of a $(-1)$-cochain is the null homotopic map of its components |

The type `CochainComplex.HomComplex.Cocycle` for $F$, $G$ and $n$ is the subgroup of cochains $z$ with $\delta z = 0$. The isomorphism `CochainComplex.HomComplex.Cocycle.equivHom` identifies morphisms of complexes with $0$-cocycles, and `CochainComplex.HomComplex.Cocycle.homOf` goes back. A homotopy between $\varphi_1$ and $\varphi_2$ is the same as a $(-1)$-cochain $z$ with $\varphi_1 = \delta z + \varphi_2$, by `CochainComplex.HomComplex.Cochain.equivHomotopy`. The definition `CochainComplex.HomComplex` assembles the groups into a cochain complex of abelian groups, and `CochainComplex.linearHomComplex` gives a complex of $R$-modules.

#### Cohomology classes

The subgroup `CochainComplex.HomComplex.coboundaries` contains the cocycles of the form $\delta \beta$, by `CochainComplex.HomComplex.mem_coboundaries_iff`. The quotient is `CochainComplex.HomComplex.CohomologyClass`, with the map `CochainComplex.HomComplex.CohomologyClass.mk` and the lemmas `CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff` and `CochainComplex.HomComplex.CohomologyClass.mk_eq_mk_iff`. Two results connect it with other objects:

| Lean name | Statement |
|---|---|
| `CochainComplex.HomComplex.homologyAddEquiv` | the homology of the Hom complex in degree $n$ is the group of cohomology classes |
| `CochainComplex.HomComplex.homologyLinearEquiv` | the same for the $R$-linear Hom complex |
| `CochainComplex.HomComplex.CohomologyClass.toHom` | a class gives a morphism $K \to L[n]$ in the homotopy category |
| `CochainComplex.HomComplex.CohomologyClass.toHom_bijective` | this map is bijective |
| `CochainComplex.HomComplex.CohomologyClass.homAddEquiv` | the resulting isomorphism of groups |

The isomorphism with the homology uses an explicit left homology data, `CochainComplex.HomComplex.leftHomologyData`, so the homology is computed with cocycles and coboundaries and not with a kernel of an abstract category.

#### Shifts

A cochain of degree $n$ from $K$ to $L$ gives cochains on the shifted complexes. The three operations have different degrees and signs:

| Lean name | Statement |
|---|---|
| `CochainComplex.HomComplex.Cochain.rightShift` | from $K$ to $L[a]$, of degree $n'$ with $n' + a = n$, with no sign on components |
| `CochainComplex.HomComplex.Cochain.leftShift` | from $K[a]$ to $L$, of degree $n'$ with $n + a = n'$, with the sign $(-1)^{a n' + a(a-1)/2}$ on components |
| `CochainComplex.HomComplex.Cochain.shift` | from $K[a]$ to $L[a]$, of the same degree |
| `CochainComplex.HomComplex.Cochain.δ_rightShift` | the differential commutes with the right shift up to $(-1)^a$ |
| `CochainComplex.HomComplex.Cochain.δ_leftShift` | the same for the left shift |
| `CochainComplex.HomComplex.Cochain.leftShift_rightShift_eq_negOnePow_rightShift_leftShift` | the two shifts commute up to $(-1)^a$ |

The inverse operations are `CochainComplex.HomComplex.Cochain.rightUnshift` and `CochainComplex.HomComplex.Cochain.leftUnshift`, with the same names for cocycles. The isomorphism `CochainComplex.HomComplex.Cocycle.equivHomShift` identifies morphisms $K \to L[n]$ with $n$-cocycles from $K$ to $L$. The lemma `CochainComplex.HomComplex.Cocycle.shiftedHomComp_equivHomShift_symm` relates it to the composition of shifted morphisms.

#### Single complexes, induction and bounds

For an object $X$ placed in degree $p$, a cochain of degree $n$ from the single complex to $K$ is the same as a map $X \to K^{p+n}$, by `CochainComplex.HomComplex.Cochain.fromSingleEquiv`. The dual is `CochainComplex.HomComplex.Cochain.toSingleEquiv`. The constructors `CochainComplex.HomComplex.Cochain.fromSingleMk` and `CochainComplex.HomComplex.Cochain.toSingleMk` build these cochains, and `CochainComplex.HomComplex.Cochain.δ_fromSingleMk` computes their differentials. The lemmas `CochainComplex.HomComplex.Cocycle.fromSingleMk_mem_coboundaries_iff` and `CochainComplex.HomComplex.Cocycle.toSingleMk_mem_coboundaries_iff` say when such a cocycle is a coboundary.

The induction module defines `CochainComplex.HomComplex.Cochain.EqUpTo`: two cochains agree up to a degree $p_0$ if their components $z_{p,q}$ agree for $p \le p_0$. A sequence of maps that changes each cochain only above a growing degree has a limit, `CochainComplex.HomComplex.Cochain.InductionUp.limitSequence`, which agrees with each term of the sequence up to its degree by `CochainComplex.HomComplex.Cochain.InductionUp.limitSequence_eqUpTo`. This builds homotopies and morphisms degree by degree.

The bounds module proves `CochainComplex.HomComplex.subsingleton_cochain`: if $K$ is zero above $p$, $L$ is zero below $q$ and $p + n < q$, then all cochains of degree $n$ are zero. With `CochainComplex.HomComplex.isStrictlyGE_linearHomComplex`, the $R$-linear Hom complex is then strictly bounded below.

#### Common errors

1. Every composition and shift takes an equation between degrees. Do not rewrite the degree of a cochain with a rewrite; the type changes and the lemmas no longer apply. Give the equation as an argument, and let the simp lemmas such as `CochainComplex.HomComplex.Cochain.comp_v` produce the components.
2. Composition is in diagrammatic order: the composition of $z_1$ from $F$ to $G$ with $z_2$ from $G$ to $K$ is a cochain from $F$ to $K$. The sign in the Leibniz rule depends on the degree of $z_2$, the second factor.
3. The left shift has a sign and the right shift has none. A proof that moves a shift from one side to the other must use `CochainComplex.HomComplex.Cochain.leftShift_rightShift_eq_negOnePow_rightShift_leftShift` or a similar lemma.

### Exercises

1. (A) Write the components of `CochainComplex.HomComplex.δ` applied to a $0$-cochain $z$ and show that $\delta z = 0$ iff $z$ commutes with the differentials.
2. (A) Show that $\delta \circ \delta = 0$ on a $0$-cochain from the component formula.
3. (B) Let $K$ be the single complex $\mathbb{Z}$ in degree $0$ and $L$ the complex $\mathbb{Z} \xrightarrow{2} \mathbb{Z}$ in degrees $0$ and $1$. Compute the cohomology classes of degrees $0$ and $1$ from $K$ to $L$.
4. (B) Use `CochainComplex.HomComplex.Cochain.equivHomotopy` to prove that a morphism of complexes whose cocycle is a coboundary is homotopic to zero.
5. (B) Prove the Leibniz rule for a $0$-cochain composed with a $1$-cochain from the component formulas.
6. (C) Use the bounds result to show that every morphism in the homotopy category from a strictly bounded above complex to a strictly bounded below complex of higher degree is zero.

### Reference

<?reference?>
