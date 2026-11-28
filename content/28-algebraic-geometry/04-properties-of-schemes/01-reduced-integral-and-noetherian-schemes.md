---
title: Reduced, integral and Noetherian schemes
kind: theory
modules:
  - Mathlib.AlgebraicGeometry.AlgClosed.Basic
  - Mathlib.AlgebraicGeometry.Artinian
  - Mathlib.AlgebraicGeometry.FunctionField
  - Mathlib.AlgebraicGeometry.Geometrically.Basic
  - Mathlib.AlgebraicGeometry.Geometrically.Connected
  - Mathlib.AlgebraicGeometry.Geometrically.Integral
  - Mathlib.AlgebraicGeometry.Geometrically.Irreducible
  - Mathlib.AlgebraicGeometry.Geometrically.Reduced
  - Mathlib.AlgebraicGeometry.Noetherian
  - Mathlib.AlgebraicGeometry.Normalization
  - Mathlib.AlgebraicGeometry.Properties
  - Mathlib.AlgebraicGeometry.QuasiAffine
explains:
  E3: [AlgebraicGeometry.IsReduced, AlgebraicGeometry.IsIntegral, AlgebraicGeometry.isIntegral_iff_irreducibleSpace_and_isReduced, AlgebraicGeometry.Scheme.functionField, AlgebraicGeometry.IsLocallyNoetherian, AlgebraicGeometry.IsNoetherian, AlgebraicGeometry.isNoetherianRing_of_away, AlgebraicGeometry.IsLocallyArtinian, AlgebraicGeometry.IsArtinianScheme, AlgebraicGeometry.Scheme.IsQuasiAffine, AlgebraicGeometry.pointEquivClosedPoint, AlgebraicGeometry.geometrically, AlgebraicGeometry.Scheme.Hom.normalization]
  E2: [AlgebraicGeometry.isReduced_of_isReduced_stalk, AlgebraicGeometry.affine_isReduced_iff, AlgebraicGeometry.basicOpen_eq_bot_iff, AlgebraicGeometry.affine_isIntegral_iff, AlgebraicGeometry.map_injective_of_isIntegral, AlgebraicGeometry.isField_stalk_of_closure_mem_irreducibleComponents, AlgebraicGeometry.genericPoint_eq_bot_of_affine, AlgebraicGeometry.functionField_isFractionRing_of_affine, AlgebraicGeometry.Scheme.germToFunctionField_injective, AlgebraicGeometry.isLocallyNoetherian_iff_of_affine_openCover, AlgebraicGeometry.isNoetherian_iff_of_finite_affine_openCover, AlgebraicGeometry.IsNoetherian.noetherianSpace, AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian, AlgebraicGeometry.IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology, AlgebraicGeometry.IsArtinianScheme.iff_isNoetherian_and_discreteTopology, AlgebraicGeometry.Scheme.IsQuasiAffine.of_isImmersion, AlgebraicGeometry.residueFieldIsoBase, AlgebraicGeometry.pointOfClosedPoint, AlgebraicGeometry.GeometricallyReduced, AlgebraicGeometry.GeometricallyIrreducible, AlgebraicGeometry.GeometricallyConnected, AlgebraicGeometry.GeometricallyIntegral, AlgebraicGeometry.GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible, AlgebraicGeometry.Scheme.Hom.toNormalization, AlgebraicGeometry.Scheme.Hom.fromNormalization, AlgebraicGeometry.Scheme.Hom.normalizationDesc, AlgebraicGeometry.Scheme.Hom.normalizationObjIso]
  E1: auto
families: []
requires: [V09.C02, V09.C03, V09.C04, V09.C06, V10.C01, V11.C04, V28.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Reduced, integral and Noetherian schemes

### Overview

A scheme is glued from rings, and many properties of rings give properties of schemes: a scheme is reduced, integral or Noetherian when it is so on affine pieces. The tasks are to show that the property does not depend on the pieces, and to extract geometry from it: an integral scheme has a generic point and a function field, and a Noetherian scheme has a Noetherian underlying space.

The section then treats Artinian and quasi-affine schemes, the properties that survive each change of base field, the closed points of a scheme of finite type over an algebraically closed field, and the relative normalization.

### Definitions

Write $\Gamma(X, U) = \mathcal{O}_X(U)$. For $s \in \Gamma(X, U)$, the *basic open* $X_s$ is the set of $x \in U$ at which the germ $s_x$ is a unit.

**Definition (Reduced scheme).** A scheme $X$ is *reduced* when $\Gamma(X, U)$ has no nonzero nilpotent elements for each open $U$.

A nilpotent function vanishes at each point, because its germ lies in each maximal ideal. On a reduced scheme a function is determined by where it vanishes, as the lemma below shows.

**Definition (Integral scheme).** A scheme $X$ is *integral* when $X$ is nonempty and $\Gamma(X, U)$ is an integral domain for each nonempty open $U$.

A space is *irreducible* when it is nonempty and not the union of two proper closed subsets. A scheme is sober: each irreducible closed set $Z$ has exactly one point $\eta$ with $\overline{\{\eta\}} = Z$, its *generic point*.

**Definition (Function field).** Let $X$ be an irreducible scheme with generic point $\eta$. The *function field* of $X$ is the stalk $K(X) = \mathcal{O}_{X,\eta}$.

**Definition (Noetherian scheme).** A scheme $X$ is *locally Noetherian* when $\Gamma(X, U)$ is a Noetherian ring for each affine open $U$. It is *Noetherian* when it is locally Noetherian and quasi-compact.

**Definition (Artinian scheme).** *Locally Artinian* and *Artinian* schemes are defined in the same way, with Artinian rings.

**Definition (Quasi-affine scheme).** A scheme $X$ is *quasi-affine* when it is quasi-compact and the canonical morphism $X \to \operatorname{Spec} \Gamma(X, X)$ is an immersion.

**Definition (Geometric property).** Let $P$ be a property of schemes. A morphism $f : X \to Y$ is *geometrically* $P$ when, for each field $K$ and each morphism $\operatorname{Spec} K \to Y$, the fiber product $X \times_Y \operatorname{Spec} K$ has $P$. With $P$ reduced, irreducible, connected or integral, this defines *geometrically reduced*, *irreducible*, *connected* and *integral* morphisms. A field extension can make a reduced scheme nonreduced, and the geometric versions rule this out.

**Definition (Relative normalization).** Let $f : X \to Y$ be quasi-compact and quasi-separated. For an affine open $U \subseteq Y$, let $A(U)$ be the integral closure of $\Gamma(Y, U)$ in $\Gamma(X, f^{-1}U)$. The *normalization of $Y$ in $X$* is the scheme $Y'$ glued from the affine schemes $\operatorname{Spec} A(U)$, with the morphisms $X \to Y'$ and $Y' \to Y$ induced by $\Gamma(Y, U) \to A(U) \to \Gamma(X, f^{-1} U)$.

### Theorems and proofs

**Proposition (Reducedness is local).** A scheme $X$ is reduced if and only if each local ring $\mathcal{O}_{X,x}$ is reduced. The affine scheme $\operatorname{Spec} R$ is reduced if and only if $R$ is reduced.

*Proof.* Suppose that the stalks are reduced and $s \in \Gamma(X, U)$ has $s^n = 0$. Then $(s_x)^n = 0$ for $x \in U$, so $s_x = 0$. A section with zero germs is zero by the sheaf axiom, so $s = 0$. Conversely, suppose that $X$ is reduced and $g \in \mathcal{O}_{X,x}$ has $g^n = 0$. Write $g = s_x$ for some $s \in \Gamma(X, U)$. The germ of $s^n$ is zero, so $s^n|_V = 0$ for an open $V \ni x$ in $U$. Then $s|_V$ is nilpotent in $\Gamma(X, V)$, hence zero, and $g = (s|_V)_x = 0$. For the second claim, $\Gamma(\operatorname{Spec} R, \operatorname{Spec} R) \cong R$ gives one direction. If $R$ is reduced, each localization $R_{\mathfrak p}$ is reduced, and these are the stalks. $\square$

**Lemma (Functions on a reduced scheme).** Let $X$ be reduced and $s \in \Gamma(X, U)$. Then $X_s = \emptyset$ if and only if $s = 0$.

*Proof.* If $s = 0$, no germ of $s$ is a unit, because the stalks are local rings and so nonzero. Suppose $X_s = \emptyset$, and let $V \subseteq U$ be an affine open, $V \cong \operatorname{Spec} A$. The basic open of $s|_V$ in $\operatorname{Spec} A$ is the set of primes that do not contain $s|_V$, and it is empty. So $s|_V$ lies in each prime of $A$, and it is nilpotent. As $A$ is reduced, $s|_V = 0$. The affine opens in $U$ cover $U$, so $s = 0$ by the sheaf axiom. $\square$

**Theorem (Integral means irreducible and reduced).** A scheme $X$ is integral if and only if its underlying space is irreducible and $X$ is reduced.

*Proof.* Let $X$ be integral. Domains and the zero ring $\Gamma(X, \emptyset)$ are reduced, so $X$ is reduced. Suppose $X = S \cup T$ with $S, T$ closed and proper. The opens $U = X \setminus S$ and $V = X \setminus T$ are nonempty and disjoint. By the sheaf axiom for a disjoint union, $\Gamma(X, U \cup V) \cong \Gamma(X, U) \times \Gamma(X, V)$. Both factors are nonzero, so the product has the zero divisor $(1, 0)$. This contradicts integrality, so $X$ is irreducible.

Conversely, let $X$ be irreducible and reduced, and let $U$ be a nonempty open. The ring $\Gamma(X, U)$ is nonzero, since a germ map sends $1$ to $1 \neq 0$. Let $a, b \in \Gamma(X, U)$ with $ab = 0$. If $X_a$ and $X_b$ are both nonempty, they are nonempty opens of an irreducible space, so they meet at some $x$. Then $a_x$ and $b_x$ are units, so $(ab)_x = 0$ is a unit of a nonzero ring, a contradiction. So $X_a = \emptyset$ or $X_b = \emptyset$, and the lemma gives $a = 0$ or $b = 0$. $\square$

**Corollary (Affine integral schemes).** $\operatorname{Spec} R$ is integral if and only if $R$ is a domain. Then the generic point is the prime $(0)$, and the function field is the field of fractions $\operatorname{Frac}(R)$.

*Proof.* If $\operatorname{Spec} R$ is integral, its global ring $R$ is a domain. If $R$ is a domain, then $R$ is reduced and $(0)$ is prime. Each prime contains $(0)$, so $\overline{\{(0)\}} = V(0) = \operatorname{Spec} R$, and the space is irreducible with generic point $(0)$. The theorem gives integrality. The stalk at $(0)$ is $R_{(0)} = \operatorname{Frac}(R)$. $\square$

**Theorem (The function field).** Let $X$ be integral with generic point $\eta$. Then $K(X)$ is a field. For each nonempty affine open $U$, the germ map $\Gamma(X, U) \to K(X)$ identifies $K(X)$ with $\operatorname{Frac} \Gamma(X, U)$. For nonempty opens $V \subseteq U$, the restriction $\Gamma(X, U) \to \Gamma(X, V)$ is injective.

*Proof.* A nonempty open $U$ is dense in the irreducible space $X$, so $\eta \in U$, since $\overline{\{\eta\}} = X$. The open $U$ is irreducible with generic point $\eta$, and it is integral. If $U \cong \operatorname{Spec} A$, the corollary shows that $\eta$ is the prime $(0)$ of the domain $A$ and $\mathcal{O}_{X,\eta} = \operatorname{Frac}(A)$. For the injectivity, let $s \in \Gamma(X, U)$ with $s|_V = 0$. Then $X_s \cap V = X_{s|_V} = \emptyset$. As $X_s$ and $V$ are opens of an irreducible space and $V \neq \emptyset$, this forces $X_s = \emptyset$, and $s = 0$ by the lemma. $\square$

**Lemma (Noetherian rings are local).** Let $R$ be a ring and $f_1, \dots, f_n \in R$ with $(f_1, \dots, f_n) = R$. If each $R_{f_i}$ is Noetherian, then $R$ is Noetherian.

*Proof.* First, an ideal $I$ is determined by its localizations: $I = \{ r \in R : r/1 \in I R_{f_i} \text{ for all } i \}$. The inclusion $\subseteq$ is clear. If $r/1 \in I R_{f_i}$ for all $i$, then $f_i^{m} r \in I$ for some $m$ and all $i$. The $f_i^{m}$ generate the unit ideal, as a prime that contains them contains all $f_i$. Write $1 = \sum c_i f_i^{m}$; then $r = \sum c_i f_i^{m} r \in I$. Now let $I_1 \subseteq I_2 \subseteq \cdots$ be a chain of ideals of $R$. For each $i$ the chain $I_k R_{f_i}$ stabilizes from an index $N_i$. For $k \geq N = \max_i N_i$ the ideals $I_k$ and $I_N$ have the same localizations, so $I_k = I_N$. $\square$

**Theorem (Noetherian schemes).** Let $X$ be a scheme and $\{U_i\}$ a cover by affine opens with $\Gamma(X, U_i)$ Noetherian. Then $X$ is locally Noetherian. If the cover is finite, $X$ is Noetherian, its underlying space is a Noetherian topological space, and $X$ has finitely many irreducible components.

*Proof.* Let $V \cong \operatorname{Spec} A$ be an affine open. Each point of $V \cap U_i$ has a neighbourhood that is a basic open both in $V$ and in $U_i$. So $V$ is covered by basic opens $D(g)$, $g \in A$, with $A_g \cong \Gamma(X, D(g))$ a localization of the Noetherian ring $\Gamma(X, U_i)$, hence Noetherian. The space $V$ is quasi-compact, so finitely many $g_1, \dots, g_n$ suffice, and they generate the unit ideal of $A$. The lemma shows that $A$ is Noetherian. If the cover is finite, $X$ is quasi-compact. The spectrum of a Noetherian ring is a Noetherian space, since closed sets correspond to radical ideals. A finite union of Noetherian subspaces is Noetherian, and a Noetherian space has finitely many irreducible components. $\square$

**Remark (Artinian schemes).** A scheme is locally Artinian if and only if it is locally Noetherian with discrete topology, so an Artinian scheme is finite. This follows from the ring fact that Artinian means Noetherian of Krull dimension $0$.

**Theorem (Closed points and rational points).** Let $k$ be algebraically closed and $f : X \to \operatorname{Spec} k$ locally of finite type. For each closed point $x$, the residue field $\kappa(x)$ is isomorphic to $k$ over $k$. Sending a section of $f$ to its image point is a bijection from the sections of $f$ to the closed points of $X$.

*Proof.* Let $x$ be closed and $x \in U \cong \operatorname{Spec} A$ affine open, with $A$ finitely generated over $k$. Then $x$ is a maximal ideal $\mathfrak m$, and by Zariski's lemma $\kappa(x) = A/\mathfrak m$ is a finite extension of $k$, so it equals $k$. The composite $\operatorname{Spec} k = \operatorname{Spec} \kappa(x) \to X$ is a section with image $x$. Conversely, let $p$ be a section with image $x$. Then $p$ factors through $\operatorname{Spec} \kappa(x)$, and $k \to \kappa(x) \to k$ is the identity, so $\kappa(x) = k$. On an affine open $\operatorname{Spec} A \ni x$, the prime $\mathfrak p$ of $x$ has $k \subseteq A/\mathfrak p \subseteq k$, so $\mathfrak p$ is maximal. A finitely generated $k$-algebra is a Jacobson ring, and so a point that is closed in one affine open of $X$ is closed in $X$. A $k$-morphism $\operatorname{Spec} k \to X$ is its image $x$ together with a $k$-map $\kappa(x) \to k$, which is unique, so the constructions are inverse. $\square$

**Proposition (Geometric properties).** A morphism is geometrically integral if and only if it is geometrically reduced and geometrically irreducible. A scheme geometrically integral over a field $K$ is integral.

*Proof.* Apply the theorem on integral schemes to each fiber product $X \times_Y \operatorname{Spec} L$. For the second claim, take $L = K$ and the identity of $\operatorname{Spec} K$; the fiber product is $X$. $\square$

**Theorem (Universal property of the normalization).** Let $f : X \to Y$ be quasi-compact and quasi-separated, with normalization $X \xrightarrow{\nu} Y' \xrightarrow{\pi} Y$. Then $\pi$ is integral with $\Gamma(Y', \pi^{-1} U) = A(U)$ for $U$ affine. If $f = f_2 \circ f_1$ with $f_1 : X \to T$ and $f_2 : T \to Y$ integral, then exactly one $g : Y' \to T$ has $g \circ \nu = f_1$ and $f_2 \circ g = \pi$.

*Proof.* Integral closure commutes with localization, and for $f$ quasi-compact and quasi-separated $\Gamma(X, f^{-1}(U_s)) = \Gamma(X, f^{-1}U)_s$. So $A(U_s) = A(U)_s$, and the pieces $\operatorname{Spec} A(U)$ glue. Over $U$ the scheme $Y'$ is $\operatorname{Spec} A(U)$, which is integral over $U$. Let $f_2$ be integral, so $f_2^{-1} U = \operatorname{Spec} B(U)$ with $B(U)$ integral over $\Gamma(Y, U)$. The image of $B(U)$ in $\Gamma(X, f^{-1} U)$ is integral over $\Gamma(Y, U)$, so it lies in $A(U)$. The ring maps $B(U) \to A(U)$ are compatible in $U$ and glue to $g$. Uniqueness holds on each piece, because $A(U) \to \Gamma(X, f^{-1} U)$ is injective. $\square$

### Examples

**Example (The integers and the line).** $\operatorname{Spec} \mathbb{Z}$ is integral and Noetherian. Its points are $(0)$ and $(p)$ for the primes $p$, the generic point is $(0)$, and the function field is $\mathbb{Q}$. In the same way $\operatorname{Spec} k[x]$ has generic point $(0)$ and function field $k(x)$.

**Example (Three nonintegral schemes).** The scheme $\operatorname{Spec} k[x]/(x^2)$ is one point. It is Artinian and irreducible, but not reduced. The scheme $\operatorname{Spec} k[x, y]/(xy)$ is reduced, since $(xy) = (x) \cap (y)$ is radical, but it is the union of the closed sets $V(x)$ and $V(y)$, so it is not irreducible. The scheme $\operatorname{Spec}(k \times k)$ is two open points: reduced and Artinian, but $(1,0)(0,1) = 0$.

**Example (A field that splits).** Let $X = \operatorname{Spec} \mathbb{C}$ over $\operatorname{Spec} \mathbb{R}$, with $\mathbb{C} = \mathbb{R}[x]/(x^2 + 1)$. Then $X$ is integral. Its base change to $\mathbb{C}$ is $\operatorname{Spec} \mathbb{C}[x]/(x^2 + 1)$, and $\mathbb{C}[x]/((x - i)(x + i)) \cong \mathbb{C} \times \mathbb{C}$ by the Chinese remainder theorem. This is two points, so $X$ is not geometrically irreducible. It is geometrically reduced, because $\mathbb{C}/\mathbb{R}$ is separable.

**Example (An inseparable extension).** Let $K = \mathbb{F}_p(t)$ and $L = K[x]/(x^p - t)$, a field. With $s$ the class of $x$, $L \otimes_K L \cong L[x]/(x^p - t) = L[x]/((x - s)^p)$, in which $x - s$ is a nonzero nilpotent. So $\operatorname{Spec} L$ is integral but not geometrically reduced over $K$.

**Example (The punctured plane).** Let $X = \mathbb{A}^2_k \setminus \{0\}$, the union of $D(x)$ and $D(y)$ in $\operatorname{Spec} k[x, y]$. A global function is an element $a$ of $k(x, y)$ with $a = g/x^m = h/y^n$ for polynomials $g, h$. Then $y^n g = x^m h$, so $x^m \mid g$ and $a \in k[x, y]$. Thus $\Gamma(X, X) = k[x, y]$, and $X \to \operatorname{Spec} k[x, y]$ is the open immersion. So $X$ is quasi-affine. It is not affine, because this map misses the origin.

### The library around it

::: mathlib
`AlgebraicGeometry.IsReduced` · `Mathlib.AlgebraicGeometry.Properties`

The field is `component_reduced : ∀ U, IsReduced Γ(X, U)`. The proposition is `isReduced_of_isReduced_stalk`, with an instance for the converse, and `affine_isReduced_iff` is the affine case. The lemma on functions is the simp lemma `basicOpen_eq_bot_iff`.

<?decl AlgebraicGeometry.IsReduced?>
:::

::: mathlib
`AlgebraicGeometry.IsIntegral` · `Mathlib.AlgebraicGeometry.Properties`

The fields are `nonempty` and `component_integral`. The theorem is `isIntegral_iff_irreducibleSpace_and_isReduced`, the affine case is `affine_isIntegral_iff`, and the injectivity of restriction is `map_injective_of_isIntegral`.

<?decl AlgebraicGeometry.IsIntegral?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.functionField` · `Mathlib.AlgebraicGeometry.FunctionField`

An abbreviation for `X.presheaf.stalk (genericPoint X)` when `[IrreducibleSpace X]`. The `Field` instance needs `[IsIntegral X]` and uses `isField_stalk_of_closure_mem_irreducibleComponents`. See also `genericPoint_eq_bot_of_affine` and `functionField_isFractionRing_of_affine`.

<?decl AlgebraicGeometry.Scheme.functionField?>
:::

::: mathlib
`AlgebraicGeometry.IsLocallyNoetherian` · `Mathlib.AlgebraicGeometry.Noetherian`

`IsNoetherian X` extends it with `CompactSpace X`. The ring lemma is `isNoetherianRing_of_away`, after Hartshorne II.3.2, and the cover criteria are `isLocallyNoetherian_iff_of_affine_openCover` and `isNoetherian_iff_of_finite_affine_openCover`. The topology comes from the instance `IsNoetherian.noetherianSpace` and `finite_irreducibleComponents_of_isNoetherian`.

<?decl AlgebraicGeometry.IsLocallyNoetherian?>
:::

::: mathlib
`AlgebraicGeometry.IsArtinianScheme` · `Mathlib.AlgebraicGeometry.Artinian`

The remark is `IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology` and `IsArtinianScheme.iff_isNoetherian_and_discreteTopology`.

<?decl AlgebraicGeometry.IsArtinianScheme?>
:::

::: mathlib
`AlgebraicGeometry.pointEquivClosedPoint` · `Mathlib.AlgebraicGeometry.AlgClosed.Basic`

For `f : X ⟶ Spec ↧K` with `[LocallyOfFiniteType f]` and `[IsAlgClosed K]`, an equivalence `{p : Spec ↧K ⟶ X // p ≫ f = 𝟙 _} ≃ closedPoints X`. The parts are `residueFieldIsoBase` and `pointOfClosedPoint`.

<?decl AlgebraicGeometry.pointEquivClosedPoint?>
:::

::: mathlib
`AlgebraicGeometry.geometrically` · `Mathlib.AlgebraicGeometry.Geometrically.Basic`

A `MorphismProperty Scheme` built from `P : ObjectProperty Scheme` with `IsPullback` squares. The classes `GeometricallyReduced`, `GeometricallyIrreducible`, `GeometricallyConnected` and `GeometricallyIntegral` wrap it, and the proposition is `GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible`.

<?decl AlgebraicGeometry.geometrically?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.IsQuasiAffine` · `Mathlib.AlgebraicGeometry.QuasiAffine`

The class extends `CompactSpace X` and `IsImmersion X.toSpecΓ`. Affine schemes are quasi-affine by an instance, and `IsQuasiAffine.of_isImmersion` passes to quasi-compact subschemes.

<?decl AlgebraicGeometry.Scheme.IsQuasiAffine?>
:::

::: mathlib
`AlgebraicGeometry.Scheme.Hom.normalization` · `Mathlib.AlgebraicGeometry.Normalization`

For `[QuasiCompact f] [QuasiSeparated f]`, glued with `toNormalization` and `fromNormalization`. The affine pieces are `normalizationObjIso`, and the factorization is `normalizationDesc`.

<?decl AlgebraicGeometry.Scheme.Hom.normalization?>
:::

Common errors of a learner: `Scheme.functionField` is defined for each irreducible scheme, and it is not a field unless the scheme is integral. `IsIntegral` here is the class of schemes, while the integral morphisms are `IsIntegralHom`. `IsNoetherian` asks quasi-compactness; an infinite disjoint union of copies of $\operatorname{Spec} \mathbb{Z}$ is only `IsLocallyNoetherian`.

### Exercises

1. (A) Show that $\operatorname{Spec} \mathbb{Z}[x]/(x^2 - 4)$ is reduced but not integral. *Hint:* $x^2 - 4 = (x - 2)(x + 2)$ in a UFD.
2. (A) Show that $\operatorname{Spec} k[x]/(x^n)$ is Artinian with one point, and that it is reduced only for $n = 1$. *Hint:* Find the primes that contain $x^n$.
3. (B) Let $X$ be integral and $U, V$ nonempty opens. Show that $U \cap V \neq \emptyset$ and that $U$, $V$, $X$ have the same function field. *Hint:* Locate the generic point.
4. (B) Let $X$ be locally Noetherian. Show that each open subscheme of $X$ is locally Noetherian. *Hint:* An affine open of $U$ is an affine open of $X$.
5. (B) Let $k$ be algebraically closed. Use the theorem on closed points to list the $k$-points of $\operatorname{Spec} k[x, y]/(xy)$. *Hint:* Closed points are maximal ideals $(x - a, y - b)$ with $ab = 0$.
6. (C) Show that $\mathbb{A}^n_k \setminus \{0\}$ is quasi-affine and not affine for $n \geq 2$, and that $\mathbb{A}^1_k \setminus \{0\}$ is affine. *Hint:* Repeat the computation of the example with $D(x_1), \dots, D(x_n)$; for $n = 1$ use $k[x, x^{-1}]$.
7. (C) With $K$ and $L$ as in the inseparable example, show that $\operatorname{Spec} L$ is geometrically irreducible over $K$. *Hint:* Over a field $M$ of characteristic $p$, the polynomial $x^p - t$ is irreducible or has a root $r$, and then it is $(x - r)^p$.

### Notes and history

Reduced and integral schemes, generic points and function fields are in Grothendieck's EGA I (1960). The local criterion for Noetherian rings follows Hartshorne, Proposition II.3.2 (1977). Geometric properties and the relative normalization are in EGA II and IV and in the Stacks project.

The Mathlib Author of `AlgebraicGeometry.Properties`, `AlgebraicGeometry.FunctionField`, `AlgebraicGeometry.Normalization`, `AlgebraicGeometry.QuasiAffine`, `AlgebraicGeometry.AlgClosed.Basic` and `AlgebraicGeometry.Geometrically.Integral`, `.Irreducible` and `.Reduced` is Andrew Yang. The Mathlib Authors of `AlgebraicGeometry.Geometrically.Basic` and `AlgebraicGeometry.Geometrically.Connected` are Timo Kraenzle, Judith Ludwig, Bryan Wang, Christian Merten, Yannis Monbru, Alireza Shavali and Chenyi Yang. The Mathlib Author of `AlgebraicGeometry.Noetherian` is Geno Racklin Asher, and the Mathlib Author of `AlgebraicGeometry.Artinian` is Brian Nugent.

### Reference

<?reference?>
