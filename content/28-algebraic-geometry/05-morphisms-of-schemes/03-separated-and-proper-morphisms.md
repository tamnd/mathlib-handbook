---
title: Separated and proper morphisms
kind: theory
modules:
  - Mathlib.AlgebraicGeometry.Morphisms.Proper
  - Mathlib.AlgebraicGeometry.Morphisms.Separated
  - Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
  - Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
  - Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
  - Mathlib.AlgebraicGeometry.ValuativeCriterion
  - Mathlib.AlgebraicGeometry.ZariskisMainTheorem
explains:
  E3: [AlgebraicGeometry.IsSeparated, AlgebraicGeometry.Scheme.IsSeparated, AlgebraicGeometry.ext_of_isDominant_of_isSeparated, AlgebraicGeometry.IsClosedImmersion.of_comp, AlgebraicGeometry.UniversallyClosed, AlgebraicGeometry.IsProper, AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom, AlgebraicGeometry.ValuativeCommSq, AlgebraicGeometry.ValuativeCriterion, AlgebraicGeometry.IsSeparated.valuativeCriterion, AlgebraicGeometry.IsProper.of_valuativeCriterion, AlgebraicGeometry.Scheme.Hom.exists_isIso_morphismRestrict_toNormalization, AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite]
  E2: [AlgebraicGeometry.Scheme.isSeparated_iff_isClosedImmersion_prod_lift, AlgebraicGeometry.isSeparated_of_injective, AlgebraicGeometry.IsAffineHom.of_comp, AlgebraicGeometry.UniversallyOpen, AlgebraicGeometry.UniversallyInjective, AlgebraicGeometry.UniversallyInjective.iff_diagonal, AlgebraicGeometry.universallyClosed_eq_universallySpecializing, AlgebraicGeometry.compactSpace_of_universallyClosed, AlgebraicGeometry.Scheme.Hom.isProperMap, AlgebraicGeometry.Flat.generalizingMap, AlgebraicGeometry.isOpenMap_of_generalizingMap, AlgebraicGeometry.isProper_eq, AlgebraicGeometry.UniversallyClosed.of_comp_of_isSeparated, AlgebraicGeometry.isField_of_universallyClosed, AlgebraicGeometry.finite_appTop_of_universallyClosed, AlgebraicGeometry.ValuativeCriterion.Existence, AlgebraicGeometry.ValuativeCriterion.Uniqueness, AlgebraicGeometry.ValuativeCriterion.iff, AlgebraicGeometry.ValuativeCriterion.Existence.eq, AlgebraicGeometry.UniversallyClosed.of_valuativeCriterion, AlgebraicGeometry.IsSeparated.of_valuativeCriterion, AlgebraicGeometry.Scheme.Hom.isOpen_quasiFiniteAt, AlgebraicGeometry.Scheme.Hom.quasiFiniteLocus, AlgebraicGeometry.Scheme.Hom.exists_mem_and_isIso_morphismRestrict_toNormalization, AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite, AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono, AlgebraicGeometry.exists_etale_isCompl_of_quasiFiniteAt]
  E1: auto
families: []
requires: [V10.C01, V10.C03, V13.C05, V28.C03, V28.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Separated and proper morphisms

### Overview

The Zariski topology is almost never Hausdorff, so the topological notion of a separated space is useless for schemes. Grothendieck replaced it by a condition on the diagonal: a topological space is Hausdorff exactly when its diagonal is closed in the product, and a morphism is separated when its diagonal is a closed immersion. In the same spirit, a compact space is one whose maps to a point stay closed after any product, and a proper morphism is a separated morphism of finite type that is universally closed. The valuative criteria test both notions with valuation rings, as sequences and limits test the topological notions.

This section defines separated, universally closed and proper morphisms, proves that the affine line with a doubled origin is not separated, proves one direction of each valuative criterion, and states Zariski's main theorem with its corollary that finite means proper and quasi-finite.

### Definitions

Let $f : X \to Y$ be a morphism and $\Delta_f : X \to X \times_Y X$ its diagonal, the morphism with $p_1 \circ \Delta_f = p_2 \circ \Delta_f = \mathrm{id}_X$.

**Definition (Separated).** The morphism $f$ is *separated* when $\Delta_f$ is a closed immersion. A scheme $X$ is *separated* when $X \to \operatorname{Spec} \mathbb{Z}$ is separated, that is, when $X \to X \times X$ is a closed immersion.

**Definition (Universally closed, open and injective).** For a property $T$ of continuous maps, a morphism $f$ is *universally* $T$ when every base change $X \times_Y Y' \to Y'$ has $T$ on underlying spaces. With $T$ closed, open or injective, this defines *universally closed*, *universally open* and *universally injective* morphisms.

**Definition (Proper).** The morphism $f$ is *proper* when it is separated, universally closed and locally of finite type.

A universally closed morphism is quasi-compact, and the index proves it, so a proper morphism is of finite type in the usual sense.

**Definition (Valuative square).** A *valuative square* for $f$ is a valuation ring $R$ with fraction field $K$ and a commutative square
$$\begin{array}{ccc} \operatorname{Spec} K & \xrightarrow{i_1} & X \\ \downarrow & & \downarrow f \\ \operatorname{Spec} R & \xrightarrow{i_2} & Y. \end{array}$$
A *lift* is a morphism $l : \operatorname{Spec} R \to X$ with $f \circ l = i_2$ that restricts to $i_1$ on $\operatorname{Spec} K$. The morphism $f$ satisfies the *existence part* of the valuative criterion when every valuative square has a lift, and the *uniqueness part* when every valuative square has at most one lift.

**Definition (Quasi-finite locus and normalization).** For $f$ locally of finite type, the *quasi-finite locus* is the set of $x \in X$ at which $f$ is quasi-finite (Section 2). For $f$ quasi-compact and quasi-separated, the *relative normalization* $X' \to Y$ is the relative spectrum of the integral closure of $\mathcal{O}_Y$ in $f_* \mathcal{O}_X$; the morphism $f$ factors as $X \to X' \to Y$ with $X' \to Y$ integral.

### Theorems and proofs

**Proposition (The diagonal is an immersion).** For every morphism $f$, the diagonal $\Delta_f$ is an immersion. If $X$ and $Y$ are affine, it is a closed immersion.

*Proof.* Let $X = \operatorname{Spec} B$ and $Y = \operatorname{Spec} A$. Then $X \times_Y X = \operatorname{Spec}(B \otimes_A B)$ and $\Delta_f$ is $\operatorname{Spec}$ of the multiplication $b \otimes b' \mapsto bb'$. It is surjective, so $\Delta_f$ is a closed immersion by Section 1. In general, cover $Y$ by affine opens $V$ and each $f^{-1}(V)$ by affine opens $U$. The sets $U \times_V U$ are affine opens of $X \times_Y X$, and $\Delta_f^{-1}(U \times_V U) = U$, since a point $x$ with $\Delta_f(x) \in U \times_V U$ has $x = p_1(\Delta_f(x)) \in U$. Let $W$ be the union of all $U \times_V U$. It is open and contains $\Delta_f(X)$. Over each $U \times_V U$ the morphism $X \to W$ restricts to the closed immersion $U \to U \times_V U$ of the affine case. Closed immersions are local on the target, so $X \to W$ is a closed immersion, and $\Delta_f$ is a closed immersion followed by an open immersion. $\square$

**Corollary (Affine morphisms are separated).** An affine morphism is separated. In particular every affine scheme is separated.

*Proof.* Separatedness is local on the target, since the diagonal of $f|_V$ is the restriction of $\Delta_f$ over the open $f^{-1}(V) \times_V f^{-1}(V)$. Over an affine $V$, the source $f^{-1}(V)$ of an affine morphism is affine, and the proposition applies. $\square$

**Theorem (Equality on a dense set).** Let $s : Y \to Z$ be separated, $X$ reduced, and $f, g : X \to Y$ with $s \circ f = s \circ g$. Let $\iota : W \to X$ be dominant with $f \circ \iota = g \circ \iota$. Then $f = g$.

*Proof.* The pair $(f, g)$ defines $h : X \to Y \times_Z Y$. Let $E = X \times_{Y \times_Z Y} Y$ be the pullback of $\Delta_s$ along $h$. Then $e : E \to X$ is a closed immersion, as a base change of a closed immersion. A morphism $t : T \to X$ factors through $E$ exactly when $f \circ t = g \circ t$, so $\iota$ factors through $E$. Hence $e(E)$ is a closed set that contains the dense set $\iota(W)$, and $e$ is surjective. A surjective closed immersion into a reduced scheme is an isomorphism: its ideal sheaf has sections that vanish at every point, so they are locally nilpotent, so they are $0$. So $e$ is an isomorphism, and $f = f \circ e \circ e^{-1} = g \circ e \circ e^{-1} = g$. $\square$

**Corollary (Uniqueness for separated morphisms).** A separated morphism satisfies the uniqueness part of the valuative criterion.

*Proof.* Let $l_1, l_2$ be two lifts of a valuative square. The scheme $\operatorname{Spec} R$ is reduced, since $R$ is a domain. The morphism $\operatorname{Spec} K \to \operatorname{Spec} R$ has image the generic point $(0)$, which is dense. The lifts agree on $\operatorname{Spec} K$ and $f \circ l_1 = i_2 = f \circ l_2$. The theorem with $s = f$ gives $l_1 = l_2$. $\square$

**Proposition (Cancellation).** Let $f : X \to Y$ and $g : Y \to Z$ with $g$ separated and $g \circ f$ a closed immersion. Then $f$ is a closed immersion.

*Proof.* Write $f = p_2 \circ \Gamma_f$, with $\Gamma_f = (\mathrm{id}, f) : X \to X \times_Z Y$ the graph. The graph is the base change of $\Delta_g : Y \to Y \times_Z Y$ along $f \times \mathrm{id} : X \times_Z Y \to Y \times_Z Y$: a point of the pullback is a pair $(x, y)$ with $f(x) = y$. So $\Gamma_f$ is a closed immersion. The projection $p_2 : X \times_Z Y \to Y$ is the base change of $g \circ f$ along $g$, so it is a closed immersion. A composite of closed immersions is a closed immersion. $\square$

The same argument, with "affine" in place of "closed immersion", shows that $f$ is affine when $g \circ f$ is affine and $g$ is separated.

**Theorem (Finite morphisms are proper).** A morphism is finite if and only if it is proper and affine.

*Proof.* Let $f$ be finite. It is affine, hence separated by the corollary, and of finite type by Section 2. Finite morphisms are stable under base change, so for universal closedness it is enough to show that a finite $f$ is closed. The claim is local on the target, so let $f$ come from $A \to B$ with $B$ finite over $A$. A closed set of $\operatorname{Spec} B$ is $V(J)$ for an ideal $J$. Let $I = J \cap A$. Then $A/I \to B/J$ is injective and integral. By lying over (Volume 10, Chapter 1), every prime of $A/I$ is the contraction of a prime of $B/J$. So the image of $V(J)$ is $V(I)$, which is closed. Conversely, a proper affine $f$ is integral, as the index proves with the integral criterion in Section 2, and of finite type, so it is finite. $\square$

**Theorem (Zariski's main theorem).** Let $f : X \to Y$ be separated, quasi-compact and locally of finite type. Then the quasi-finite locus $U$ of $f$ is open, and $U \to X'$ is an open immersion into the relative normalization.

The index proves the theorem in Grothendieck's form, after an étale localization that splits off a finite part of the fiber. This handbook does not reproduce the proof.

**Corollary (Finite means proper and quasi-finite).** A morphism is finite if and only if it is proper and locally quasi-finite.

*Proof.* A finite morphism is proper by the last theorem and quasi-finite by Section 2. Conversely, let $f$ be proper and quasi-finite. Then the quasi-finite locus is $X$, and by Zariski's main theorem $j : X \to X'$ is an open immersion. The morphism $\nu : X' \to Y$ is integral, hence affine and separated. Since $\nu \circ j = f$ is universally closed and $\nu$ is separated, $j$ is universally closed, so $j(X)$ is open and closed in $X'$. So $j$ is an isomorphism onto an open and closed subscheme, and $j$ is a closed immersion, hence integral. Then $f = \nu \circ j$ is integral and of finite type, so finite by Section 2. $\square$

### Examples

**Counterexample (The doubled origin).** Let $U_1 = \operatorname{Spec} k[x]$ and $U_2 = \operatorname{Spec} k[y]$, and glue them along $D(x) \cong D(y)$ by $x \mapsto y$. The result $X$ is the affine line with the origin doubled. Over $k$, the product $X \times X$ is covered by the four opens $U_i \times U_j \cong \mathbb{A}^2$. Consider $U_1 \times U_2 = \operatorname{Spec} k[x, y]$. The preimage of it under $\Delta$ is $U_1 \cap U_2$, the line minus the origin, and $\Delta$ there is $t \mapsto (t, t)$. Its image is $V(x - y) \setminus \{(x, y)\}$, the diagonal line minus the origin. The line $V(x - y) \cong \mathbb{A}^1$ is irreducible, so the closure of the nonempty open subset is all of $V(x - y)$, which contains the origin $(x, y)$. So $\Delta(X) \cap (U_1 \times U_2)$ is not closed in $U_1 \times U_2$, $\Delta(X)$ is not closed, and $X$ is not separated. The theorem on equality on a dense set fails too: the two inclusions $j_1, j_2 : \mathbb{A}^1 \to X$ agree on the dense open $D(x)$, and $\mathbb{A}^1$ is reduced, but $j_1 \neq j_2$, since they send the origin to the two different origins. In valuative terms, with $R = k[x]_{(x)}$, a map $\operatorname{Spec} K \to X$ has two lifts.

**Counterexample (The line is not universally closed).** The morphism $\mathbb{A}^1_k \to \operatorname{Spec} k$ is closed, since its target is one point. Its base change along $\mathbb{A}^1_k \to \operatorname{Spec} k$ is the projection $\mathbb{A}^2_k \to \mathbb{A}^1_k$, $(x, y) \mapsto x$. The hyperbola $V(xy - 1)$ is closed. Over a prime $\mathfrak{p}$ of $k[x]$, its fiber is $\operatorname{Spec} \kappa(\mathfrak{p})[y]/(xy - 1)$, which is one point when $x \notin \mathfrak{p}$ and empty when $x \in \mathfrak{p}$, because then $xy - 1 = -1$. So the image is $D(x)$, which is not closed. So $\mathbb{A}^1_k$ is not proper over $k$. This is the hyperbola of Section 2 again.

**Example (The projective line is proper).** Let $\mathbb{P}^1_A$ be glued from $\operatorname{Spec} A[t]$ and $\operatorname{Spec} A[u]$ along $u = t^{-1}$. It is of finite type over $A$, quasi-compact, and separated (Exercise 3). For the existence part, take a valuative square. The point $i_1$ is $[a : b]$ with $a, b \in K$ not both $0$; let $v$ be the valuation of $R$. If $v(a) \leq v(b)$, then $a \neq 0$, and $[a : b] = [1 : b/a]$ with $b/a \in R$. The point lies in the chart $\operatorname{Spec} A[t]$ with $t = b/a$, and the ring map $A[t] \to R$ that extends $A \to R$ by $t \mapsto b/a$ gives the lift. If $v(b) < v(a)$, use the other chart with $u = a/b$. So $\mathbb{P}^1_A$ is proper over $A$ by the valuative criterion. The index has a general instance: $\operatorname{Proj} \mathcal{A} \to \operatorname{Spec} \mathcal{A}_0$ is proper when $\mathcal{A}$ is finitely generated over $\mathcal{A}_0$.

### The library around it

::: mathlib
`AlgebraicGeometry.IsSeparated` · `Mathlib.AlgebraicGeometry.Morphisms.Separated`

The field is `isClosedImmersion_diagonal`. `Scheme.IsSeparated X` is the absolute class, and `Scheme.isSeparated_iff_isClosedImmersion_prod_lift` restates it with `prod.lift (𝟙 X) (𝟙 X)`. `isSeparated_of_injective` says that an injective morphism into a separated scheme gives a separated source. `IsClosedImmersion.of_comp` and `IsAffineHom.of_comp` are the cancellation results.

<?decl AlgebraicGeometry.IsSeparated?>
:::

::: mathlib
`AlgebraicGeometry.ext_of_isDominant_of_isSeparated` · `Mathlib.AlgebraicGeometry.Morphisms.Separated`

The arguments are `[IsReduced X]`, `(s : Y ⟶ Z) [IsSeparated s]`, `f ≫ s = g ≫ s`, `(ι : W ⟶ X) [IsDominant ι]` and `ι ≫ f = ι ≫ g`. The conclusion is `f = g`.

<?decl AlgebraicGeometry.ext_of_isDominant_of_isSeparated?>
:::

::: mathlib
`AlgebraicGeometry.UniversallyClosed` · `Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed`

The field is `universally_isClosedMap`, with `MorphismProperty.universally`. `universallyClosed_eq_universallySpecializing` writes it as universally specializing and quasi-compact. `compactSpace_of_universallyClosed` gives a quasi-compact source over a field, and `Scheme.Hom.isProperMap` makes the underlying map proper. `UniversallyOpen` and `UniversallyInjective` are parallel; `UniversallyInjective.iff_diagonal` says that a morphism is universally injective exactly when its diagonal is surjective. In `Morphisms.UniversallyOpen`, `Flat.generalizingMap` and `isOpenMap_of_generalizingMap` together say that a flat morphism locally of finite presentation is open.

<?decl AlgebraicGeometry.UniversallyClosed?>
:::

::: mathlib
`AlgebraicGeometry.IsProper` · `Mathlib.AlgebraicGeometry.Morphisms.Proper`

The class extends `IsSeparated f`, `UniversallyClosed f` and `LocallyOfFiniteType f`, and `isProper_eq` writes it as an infimum. `IsFinite.iff_isProper_and_isAffineHom` is the theorem on finite morphisms. `UniversallyClosed.of_comp_of_isSeparated` is the cancellation step in the last corollary. For an integral scheme universally closed over a field `K`, `finite_appTop_of_universallyClosed` says that `Γ(X, ⊤)` is finite over `K`, and `isField_of_universallyClosed` that it is a field.

<?decl AlgebraicGeometry.IsProper?>
:::

::: mathlib
`AlgebraicGeometry.ValuativeCriterion` · `Mathlib.AlgebraicGeometry.ValuativeCriterion`

A `ValuativeCommSq f` holds `R`, `K`, `i₁`, `i₂` and `commSq`. `ValuativeCriterion.Existence` and `ValuativeCriterion.Uniqueness` are the two parts, and `ValuativeCriterion.iff` splits the full criterion into them. `ValuativeCriterion.Existence.eq` says that existence is the same as being universally specializing. The criteria are `UniversallyClosed.of_valuativeCriterion` with `[QuasiCompact f]`, `IsSeparated.of_valuativeCriterion` with `[QuasiSeparated f]`, and `IsProper.of_valuativeCriterion` with `[QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]`. `IsSeparated.valuativeCriterion` is the uniqueness corollary.

<?decl AlgebraicGeometry.ValuativeCriterion?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.Hom.exists_isIso_morphismRestrict_toNormalization` · `Mathlib.AlgebraicGeometry.ZariskisMainTheorem`

Under `[LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f]`, this gives an open `U` of `f.normalization` with `IsIso (f.toNormalization ∣_ U)` and preimage the quasi-finite points. `Scheme.Hom.isOpen_quasiFiniteAt` needs only `LocallyOfFiniteType f`, and `Scheme.Hom.quasiFiniteLocus` is the open set. The pointwise step is `Scheme.Hom.exists_mem_and_isIso_morphismRestrict_toNormalization`, and the étale localization is `exists_etale_isCompl_of_quasiFiniteAt`. The corollaries are `IsFinite.of_isProper_of_locallyQuasiFinite`, `IsFinite.iff_isProper_and_locallyQuasiFinite` and `IsClosedImmersion.iff_isProper_and_mono`.

<?decl AlgebraicGeometry.Scheme.Hom.exists_isIso_morphismRestrict_toNormalization?>
:::

Common errors of a learner: `IsSeparated f` is a property of the morphism, and a scheme is separated through `Scheme.IsSeparated`. A universally closed morphism need not be of finite type, so `UniversallyClosed` alone is weaker than `IsProper`. The valuative criteria in the index quantify over all valuation rings, not only discrete ones; the discrete form needs Noetherian hypotheses, and the index of this edition has no declaration for it. Zariski's main theorem needs `IsSeparated f` and `QuasiCompact f`.

### Exercises

1. (A) Show that an open immersion and a closed immersion are separated. *Hint:* For a monomorphism, the diagonal is an isomorphism.
2. (A) Show that a composite of separated morphisms is separated. *Hint:* Factor $\Delta_{g \circ f}$ through $X \times_Y X \to X \times_Z X$, a base change of $\Delta_g$.
3. (B) Show that $\mathbb{P}^1_A$ is separated. *Hint:* Over $\operatorname{Spec} A[t] \times_A \operatorname{Spec} A[u]$ the diagonal is $\operatorname{Spec}$ of $A[t, u] \to A[t, t^{-1}]$, $u \mapsto t^{-1}$, which is surjective.
4. (B) Show that the doubled origin fails the existence part of the valuative criterion over $k$. *Hint:* Take $K = k(x)$, $R$ the localization of $k[x^{-1}]$ at $(x^{-1})$, and the point $x$; the point at infinity is missing in both charts.
5. (C) Show that a closed immersion is proper and that a proper monomorphism is a closed immersion. *Hint:* For the second part, use the corollary on finite morphisms and Section 2.
6. (C) Let $X$ be integral and proper over a field $k$. Show that every element of $\Gamma(X, \mathcal{O}_X)$ is algebraic over $k$, and that $\Gamma(X, \mathcal{O}_X)$ is a field. *Hint:* A global section $s$ gives $X \to \mathbb{A}^1_k$ with closed irreducible image. If the image is $\mathbb{A}^1_k$, then $\mathbb{A}^1_k$ is universally closed over $k$. A domain algebraic over $k$ is a field.

### Notes and history

The notions of separated and proper morphisms and the valuative criteria are due to Grothendieck in EGA, 1960 to 1967. Zariski proved his main theorem in 1949 for varieties; Grothendieck gave the form for quasi-finite morphisms in EGA. Hartshorne (1977) states the valuative criteria for Noetherian schemes.

The Mathlib Author of `Morphisms.UniversallyClosed` and `ZariskisMainTheorem` is Andrew Yang. The Mathlib Author of `Morphisms.UniversallyOpen` is Christian Merten. The Mathlib Authors of `Morphisms.Proper` and `Morphisms.Separated` are Christian Merten and Andrew Yang. The Mathlib Authors of `Morphisms.UniversallyInjective` are Andrew Yang and Justus Springer. The Mathlib Authors of `ValuativeCriterion` are Andrew Yang, Qi Ge and Christian Merten.

### Reference

<?reference?>
