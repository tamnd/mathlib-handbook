---
title: t-structures and truncations
kind: api
modules:
  - Mathlib.CategoryTheory.Triangulated.TStructure.Basic
  - Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
  - Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
  - Mathlib.CategoryTheory.Triangulated.TStructure.ETrunc
  - Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
  - Mathlib.CategoryTheory.Triangulated.TStructure.Heart
  - Mathlib.CategoryTheory.Triangulated.TStructure.AbelianSubcategory
  - Mathlib.CategoryTheory.Triangulated.TStructure.Induced
  - Mathlib.CategoryTheory.Triangulated.TStructure.TExact
explains:
  E2: [CategoryTheory.Triangulated.TStructure, CategoryTheory.Triangulated.TStructure.zero_of_isLE_of_isGE, CategoryTheory.Triangulated.TStructure.truncLT, CategoryTheory.Triangulated.TStructure.triangleLTGE_distinguished, CategoryTheory.Triangulated.TStructure.isLE_iff_orthogonal, CategoryTheory.Triangulated.TStructure.isLE₂, CategoryTheory.Triangulated.TStructure.truncGELTIsoLTGE, CategoryTheory.Triangulated.TStructure.spectralObject, CategoryTheory.Triangulated.AbelianSubcategory.abelian, CategoryTheory.Functor.LeftTExact.mk]
  E1: auto
families: []
requires: [V24.C08, V25.C02, V25.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## t-structures and truncations

### Overview

The derived category $D(A)$ of an abelian category $A$ contains $A$ as the complexes with cohomology in degree $0$ only. Each complex $K$ has truncations $\tau_{\le n} K$ and $\tau_{\ge n+1} K$, and a distinguished triangle $\tau_{\le n} K \to K \to \tau_{\ge n+1} K \to (\tau_{\le n} K)[1]$. A t-structure axiomatizes this situation in a triangulated category. It is a pair of families of subcategories, $C^{\le n}$ and $C^{\ge n}$, with an orthogonality condition and the existence of such triangles. From these few axioms come truncation functors, a heart, and a spectral object for each object.

The modules of this section give the definition, the truncation functors with indices in $\mathbb{Z}$ and in the extended integers, the spectral object of an object, the heart, a criterion for an additive subcategory of a triangulated category to be abelian, induced t-structures on subcategories, and t-exact functors. The library does not yet show that the heart of a t-structure is abelian. The criterion of the module `Mathlib.CategoryTheory.Triangulated.TStructure.AbelianSubcategory` is the tool for that result.

In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`. The shift of $X$ by $n$ is $X[n]$, written `X⟦n⟧`. The convention is cohomological: $X[1]$ moves the cohomology of $X$ one step down.

### The library around it

#### The definition

The module `Mathlib.CategoryTheory.Triangulated.TStructure.Basic` defines the structure `Triangulated.TStructure C` for a pretriangulated category $C$. A t-structure is data, not a class, because one category can carry several t-structures. Its fields are:

1. object properties `t.le n` and `t.ge n` for $n \in \mathbb{Z}$, closed under isomorphisms;
2. `le_shift` and `ge_shift`: if $X$ is in `t.le n` and $a + n' = n$, then $X[a]$ is in `t.le n'`, and the same for `t.ge`;
3. `zero'`: every morphism from an object of `t.le 0` to an object of `t.ge 1` is zero;
4. `le_zero_le` and `ge_one_le`: `t.le 0 ≤ t.le 1` and `t.ge 1 ≤ t.ge 0`;
5. `exists_triangle_zero_one`: each object $A$ lies in a distinguished triangle $X \to A \to Y \to X[1]$ with $X$ in `t.le 0` and $Y$ in `t.ge 1`.

The classes `t.IsLE X n` and `t.IsGE X n` wrap membership, so that instances can track bounds. The lemmas `TStructure.isLE_shift_iff` and `TStructure.isGE_shift_iff` move a bound through a shift, `TStructure.le_monotone` and `TStructure.ge_antitone` compare different $n$, and `TStructure.exists_triangle` gives a triangle with $X \le n_0$ and $Y \ge n_1$ for $n_0 + 1 = n_1$.

**Lemma.** If $X \le n_0$, $Y \ge n_1$ and $n_0 < n_1$, then every $f : X \to Y$ is zero. This is `TStructure.zero_of_isLE_of_isGE`.

*Proof.* Shift by $n_0$: $X[n_0]$ is $\le 0$, and $Y[n_0]$ is $\ge n_1 - n_0 \ge 1$, by the shift axioms and the monotonicity. So $f[n_0]$ is zero by the axiom `zero'`, and $f$ is zero because the shift is an equivalence. $\square$

An object that is $\le n_0$ and $\ge n_1$ with $n_0 < n_1$ is zero, by `TStructure.isZero`: its identity is a morphism of that form. The properties `t.minus`, `t.plus` and `t.bounded` hold the objects that are $\le n$ for some $n$, $\ge n$ for some $n$, or both. Instances show that they are triangulated subcategories.

#### Truncation functors

The module `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE` builds the truncations. For $n \in \mathbb{Z}$ there are functors `t.truncLT n` and `t.truncGE n` from $C$ to $C$, with natural transformations `t.truncLTι n` to the identity, `t.truncGEπ n` from the identity, and `t.truncGEδLT n` from the second to the shift of the first. The object $\tau_{<n} X$ is $\le n - 1$, the object $\tau_{\ge n} X$ is $\ge n$, and the triangle `t.triangleLTGE n` of $X$ is

$$\tau_{< n} X \to X \to \tau_{\ge n} X \to (\tau_{< n} X)[1].$$

**Theorem.** This triangle is distinguished, and it is unique up to a unique isomorphism. The first statement is `TStructure.triangleLTGE_distinguished`, and the second is the content of `TStructure.triangle_iso_exists`.

*Proof sketch.* The key fact is that $\mathrm{Hom}(X', Y') = 0$ and $\mathrm{Hom}(X', Y'[-1]) = 0$ for $X' \le n - 1$ and $Y' \ge n$. Let $X' \to A \to Y' \to X'[1]$ and $X'' \to B \to Y'' \to X''[1]$ be two triangles of this form, and let $\varphi : A \to B$. The composite $X' \to A \to B \to Y''$ is zero, so the composite $X' \to B$ lifts to $X'$ through $X'' \to B$, by the long exact sequence of $\mathrm{Hom}(X', -)$. The lift is unique because $\mathrm{Hom}(X', Y''[-1]) = 0$. The completion axiom then extends it to a morphism of triangles, and the dual argument makes the third component unique. With $\varphi = 1$ in both directions, the two triangles are isomorphic. This uniqueness makes $\tau_{<n}$ and $\tau_{\ge n}$ functors, by a choice of one triangle for each object. $\square$

The universal properties follow. For $X \le n_0$ and $n_0 + 1 = n_1$, a morphism $f : X \to Y$ lifts uniquely to $X \to \tau_{< n_1} Y$, which is `TStructure.liftTruncLT`. For $Y \ge n$, a morphism $X \to Y$ factors uniquely through $\tau_{\ge n} X$, which is `TStructure.descTruncGE`. The natural transformation `TStructure.natTransTruncLTOfLE` compares $\tau_{<a}$ and $\tau_{<b}$ for $a \le b$.

**Proposition.** For $n_0 + 1 = n_1$, an object $X$ is $\le n_0$ if and only if every morphism from $X$ to an object $Y \ge n_1$ is zero. This is `TStructure.isLE_iff_orthogonal`, and `TStructure.isGE_iff_orthogonal` is the dual.

*Proof.* One direction is `TStructure.zero_of_isLE_of_isGE`. Conversely, apply the condition to $\pi : X \to \tau_{\ge n_1} X$. Then $\pi = 0$, and by the universal property of $\pi$ the identity of $\tau_{\ge n_1} X$ is zero. So $\tau_{\ge n_1} X$ is zero, and the triangle gives $\tau_{< n_1} X \cong X$, which is $\le n_0$. The middle step is `TStructure.isLE_iff_isZero_truncGE_obj`. $\square$

So `t.le n` is the left orthogonal of `t.ge (n + 1)`, and it is closed under extensions: in a distinguished triangle $X_1 \to X_2 \to X_3 \to X_1[1]$ with $X_1$ and $X_3$ at most $n$, the object $X_2$ is at most $n$. This is `TStructure.isLE₂`, and `TStructure.isGE₂` is the dual. Both follow from the long exact sequence of $\mathrm{Hom}(-, Y)$ and the orthogonality.

For $a, b \in \mathbb{Z}$ the abbreviations `t.truncGELT a b` and `t.truncLTGE a b` are $\tau_{\ge a} \tau_{< b}$ and $\tau_{< b} \tau_{\ge a}$. When $C$ satisfies the octahedral axiom, `TStructure.truncGELTIsoLTGE` identifies them. The proof compares the two triangles that the octahedral axiom builds from $\tau_{<a} X \to \tau_{<b} X \to X$ and uses the uniqueness of truncation triangles.

#### Other indices and the spectral object

The module `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT` gives the variants `t.truncLE n` and `t.truncGT n`, for $\le n$ and $> n$. They are defined as $\tau_{<n+1}$ and $\tau_{\ge n+1}$, and `TStructure.truncLEIsoTruncLT` and `TStructure.truncGTIsoTruncGE` are the identifications for $a + 1 = b$. The module repeats the API for these functors: the triangles `TStructure.triangleLEGT` and `TStructure.triangleLEGE`, and the composites `t.truncGELE a b` with the isomorphism `TStructure.truncGELEIsoLEGE`.

The module `Mathlib.CategoryTheory.Triangulated.TStructure.ETrunc` extends the indices to `EInt`, the integers with $-\infty$ and $+\infty$. The functors `t.eTruncLT` and `t.eTruncGE` go from `EInt` to the endofunctors of $C$. The truncation $\tau_{<-\infty}$ is zero and $\tau_{<+\infty}$ is the identity, and dually for $\tau_{\ge}$. The functor `t.eTriangleLTGE` gives the truncation triangles, and `TStructure.eTruncLTGEIsoGELT` commutes the two truncations, as in the integer case.

The module `Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject` uses these functors. The functor `t.ω₁` sends an arrow $a \le b$ of `EInt` to $\tau_{\ge a} \tau_{< b}$, which keeps the cohomology in the degrees $n$ with $a \le n < b$. For $a \le b \le c$ the connecting morphism `t.ω₁δ` goes from $\tau_{\ge b} \tau_{< c}$ to the shift of $\tau_{\ge a} \tau_{< b}$, and `TStructure.triangleω₁δ` is the triangle

$$\tau_{\ge a} \tau_{< b} X \to \tau_{\ge a} \tau_{< c} X \to \tau_{\ge b} \tau_{< c} X \to (\tau_{\ge a} \tau_{< b} X)[1].$$

**Theorem.** For a triangulated $C$ and an object $X$, these triangles are distinguished and natural in $a \le b \le c$, so they form a spectral object `t.spectralObject X` of `Triangulated.SpectralObject C EInt` in the sense of Section 6. The construction is functorial in $X$, through `t.spectralObjectFunctor`.

The proof of distinguishedness uses the octahedral axiom for $\tau_{<b} X \to \tau_{<c} X$ after $\tau_{\ge a}$, together with the commutation of the two kinds of truncation.

#### The heart and abelian subcategories

The module `Mathlib.CategoryTheory.Triangulated.TStructure.Heart` defines `t.heart`, the objects that are $\le 0$ and $\ge 0$, with `TStructure.mem_heart_iff`. In applications the heart is a known category, such as $A$ inside $D(A)$. So the class `t.Heart H` says that an additive category $H$ has a fully faithful additive functor `t.ιHeart` to $C$ whose essential image is the heart. The definition `TStructure.hasHeartFullSubcategory` gives the default choice, the full subcategory of `t.heart`.

The module `Mathlib.CategoryTheory.Triangulated.TStructure.AbelianSubcategory` gives a criterion. Let $\iota : A \to C$ be fully faithful and additive, with $C$ triangulated. Assume that every morphism $\iota X \to (\iota Y)[n]$ with $n < 0$ is zero. Call $f_1 : X_1 \to X_2$ in $A$ admissible, `AbelianSubcategory.admissibleMorphism ι`, if the cone $X_3$ of $\iota f_1$ lies in a distinguished triangle $(\iota K)[1] \to X_3 \to \iota Q \to (\iota K)[2]$ for some $K$ and $Q$ of $A$.

**Theorem.** If every morphism of $A$ is admissible, then $A$ is abelian. This is `Triangulated.AbelianSubcategory.abelian`.

*Proof sketch.* For an admissible $f_1$, the composite $(\iota K)[1] \to X_3 \to (\iota X_1)[1]$ is the shift of a morphism $K \to X_1$, which is `AbelianSubcategory.ιK`, and the composite $\iota X_2 \to X_3 \to \iota Q$ comes from a morphism $X_2 \to Q$, which is `AbelianSubcategory.πQ`. The vanishing of negative morphisms makes $K \to X_1$ a kernel of $f_1$ and $X_2 \to Q$ a cokernel, which are `AbelianSubcategory.isLimitKernelFork` and `AbelianSubcategory.isColimitCokernelCofork`. In particular `AbelianSubcategory.hasKernel_of_admissibleMorphism` holds. The octahedral axiom then shows that the image and the coimage agree. $\square$

For the heart, the hypothesis on negative morphisms is `TStructure.zero_of_isLE_of_isGE`, and admissibility comes from the truncations of the cone. This last step is the part of the theory that the library does not yet record.

#### Induced t-structures and t-exact functors

The module `Mathlib.CategoryTheory.Triangulated.TStructure.Induced` restricts a t-structure to a triangulated subcategory $P$. The class `P.HasInducedTStructure t` asks that each object of $P$ has a truncation triangle whose ends are isomorphic to objects of $P$. Under this class `P.tStructure t` is a t-structure on the full subcategory, and `ObjectProperty.tStructure_isLE_iff` says that its bounds are those of $C$. The definitions `t.onPlus`, `t.onMinus` and `t.onBounded` apply this to the bounded subcategories, which are stable under the truncations.

The module `Mathlib.CategoryTheory.Triangulated.TStructure.TExact` treats a triangulated functor $F : C \to D$ between categories with t-structures $t_1$ and $t_2$. The class `F.LeftTExact t₁ t₂` says that $X \ge n$ implies $F X \ge n$, and `F.RightTExact t₁ t₂` says that $X \le n$ implies $F X \le n$. The class `F.TExact t₁ t₂` asks both. The constructor `Functor.LeftTExact.mk` needs the condition for $n = 0$ only: for $X \ge n$, the object $X[n]$ is $\ge 0$, so $F(X[n]) \cong (FX)[n]$ is $\ge 0$, and $FX$ is $\ge n$.

#### Common errors

1. `t.truncLT n` keeps the degrees $< n$, so its values are `IsLE` with bound $n - 1$, not $n$. Use `t.truncLE n` and `TStructure.truncLEIsoTruncLT` when the bound $n$ is wanted.
2. The shift axioms read `a + n' = n`: the shift by $a$ of an object $\le n$ is $\le n - a$. A shift by $1$ lowers the bounds, in the cohomological convention.
3. `TStructure.truncGELTIsoLTGE`, the spectral object and the abelian criterion need `IsTriangulated C`, not only `Pretriangulated C`. Without the octahedral axiom the instance search fails with a message about `IsTriangulated`.

### Exercises

1. (A) Show from the axioms that `t.le n ≤ t.le (n + 1)` for every $n$, using the shift axioms and `le_zero_le`.
2. (A) Show that the zero object is in `t.heart` and that the heart is closed under finite biproducts.
3. (B) Let $X$ be in the heart. Compute $\tau_{<0} X$, $\tau_{\ge 0} X$, $\tau_{<1} X$ and $\tau_{\ge 1} X$ up to isomorphism.
4. (B) Prove `TStructure.isGE₂` from `TStructure.isGE_iff_orthogonal` and the long exact sequence of a representable functor.
5. (B) Let $F$ be t-exact. Show that $F$ sends the heart of $t_1$ into the heart of $t_2$, and that it commutes with $\tau_{<n}$ up to isomorphism.
6. (C) Let $X \to Y \to Z \to X[1]$ be distinguished with $X$, $Y$ and $Z$ in the heart. Show that $0 \to X \to Y \to Z \to 0$ is a short exact sequence for the criterion of `Triangulated.AbelianSubcategory.abelian`, granted that the heart satisfies its hypotheses.

### Reference

<?reference?>
