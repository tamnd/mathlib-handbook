---
title: Sheafification
kind: theory
modules:
  - Mathlib.CategoryTheory.Sites.Plus
  - Mathlib.CategoryTheory.Sites.ConcreteSheafification
  - Mathlib.CategoryTheory.Sites.Sheafification
  - Mathlib.CategoryTheory.Sites.LeftExact
  - Mathlib.CategoryTheory.Sites.Abelian
explains:
  E3: [CategoryTheory.GrothendieckTopology.plusObj, CategoryTheory.GrothendieckTopology.toPlus, CategoryTheory.GrothendieckTopology.Plus.sep, CategoryTheory.GrothendieckTopology.Plus.isSheaf_of_sep, CategoryTheory.GrothendieckTopology.Plus.isSheaf_plus_plus, CategoryTheory.HasSheafify, CategoryTheory.presheafToSheaf, CategoryTheory.sheafificationAdjunction, CategoryTheory.sheafIsAbelian]
  E2: [CategoryTheory.GrothendieckTopology.diagram, CategoryTheory.GrothendieckTopology.plusMap, CategoryTheory.GrothendieckTopology.plusFunctor, CategoryTheory.GrothendieckTopology.isIso_toPlus_of_isSheaf, CategoryTheory.GrothendieckTopology.plusLift, CategoryTheory.GrothendieckTopology.toPlus_plusLift, CategoryTheory.GrothendieckTopology.plusLift_unique, CategoryTheory.GrothendieckTopology.plusMap_toPlus, CategoryTheory.Meq, CategoryTheory.GrothendieckTopology.Plus.exists_rep, CategoryTheory.GrothendieckTopology.Plus.toPlus_eq_mk, CategoryTheory.GrothendieckTopology.Plus.inj_of_sep, CategoryTheory.GrothendieckTopology.Plus.exists_of_sep, CategoryTheory.GrothendieckTopology.sheafify, CategoryTheory.GrothendieckTopology.toSheafify, CategoryTheory.GrothendieckTopology.sheafify_isSheaf, CategoryTheory.plusPlusSheaf, CategoryTheory.plusPlusAdjunction, CategoryTheory.HasWeakSheafify, CategoryTheory.sheafify, CategoryTheory.toSheafify, CategoryTheory.isIso_toSheafify, CategoryTheory.isoSheafify, CategoryTheory.sheafifyLift, CategoryTheory.toSheafify_sheafifyLift, CategoryTheory.sheafifyLift_unique, CategoryTheory.GrothendieckTopology.preservesFiniteLimits_plusFunctor, CategoryTheory.GrothendieckTopology.preservesFiniteLimits_sheafification, CategoryTheory.preservesFiniteLimits_presheafToSheaf, CategoryTheory.plusPlusSheafIsoPresheafToSheaf, CategoryTheory.SheafOfTypes.balanced, CategoryTheory.SheafOfTypes.finitary_extensive, CategoryTheory.presheafToSheaf_additive]
  E1: auto
families: []
requires: [V24.C04, V24.C05, V24.C08, V25.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Sheafification

### Overview

Many natural presheaves are not sheaves. The constant presheaf with value $\mathbb{Z}$, the presheaf image of a morphism of sheaves and the presheaf cokernel of a morphism of sheaves of abelian groups are examples. Each presheaf $P$ has a best approximation by a sheaf: a sheaf $aP$ with a morphism $P \to aP$, through which each morphism from $P$ to a sheaf factors in exactly one way. In the language of Volume 24, Chapter 5, the inclusion of sheaves into presheaves has a left adjoint, and the sheaves form a reflective subcategory.

This section constructs $aP$ by the plus construction of Grothendieck. The plus construction replaces the values of $P$ by classes of compatible families on covering sieves. One application makes each presheaf separated, and a second application makes each separated presheaf a sheaf. The section then proves that sheafification preserves finite limits, and that the sheaves with values in an abelian category form an abelian category.

In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`. The notation of Section 2 is kept: $s|_f$ is the restriction of $s$ along $f$.

### Definitions

Let $J$ be a Grothendieck topology on $C$ and let $P$ be a presheaf of sets.

**Definition (Matching families).** For a covering sieve $S$ on $X$, let $\mathrm{Match}(S, P)$ be the set of compatible families of elements of $P$ for $S$. If $R \subseteq S$ are covering sieves, the restriction of families gives a map $\mathrm{Match}(S, P) \to \mathrm{Match}(R, P)$.

The covering sieves on $X$ are a directed set for reverse inclusion, because the intersection of two covering sieves is covering (Section 1). So the colimit below is a filtered colimit.

**Definition (Plus construction).** The presheaf $P^+$ has the value

$$P^+(X) = \operatorname{colim}_{S \in J(X)} \mathrm{Match}(S, P),$$

where the colimit is over the covering sieves of $X$, ordered by reverse inclusion. An element of $P^+(X)$ is a class $[S, x]$ of a covering sieve $S$ and a family $x \in \mathrm{Match}(S, P)$. Two classes $[S, x]$ and $[T, y]$ are equal if and only if there is a covering sieve $R \subseteq S \cap T$ on which $x$ and $y$ have the same restriction.

For $h : Y \to X$, the restriction is $[S, x]|_h = [h^* S, h^* x]$, where $(h^* x)_g = x_{h \circ g}$ for $g$ in $h^* S$. The map $\theta_P : P \to P^+$ sends $s \in P(X)$ to $[\top, (s|_f)_f]$.

**Definition (Sheafification).** The *sheafification* of $P$ is $aP = P^{++} = (P^+)^+$, with the morphism $\eta_P = \theta_{P^+} \circ \theta_P : P \to aP$.

For a presheaf with values in a category $D$, the same formulas make sense when $D$ has the multiequalizers that define $\mathrm{Match}(S, P)$ and the colimits over the covering sieves. Mathlib uses this general form.

::: mathlib
`CategoryTheory.GrothendieckTopology.plusObj` · `Mathlib.CategoryTheory.Sites.Plus`

`J.diagram P X` is the functor on `(J.Cover X)ᵒᵖ` that sends a cover `S` to the multiequalizer `multiequalizer (S.index P)`, which is $\mathrm{Match}(S, P)$. Then `J.plusObj P` has the value `colimit (J.diagram P X)` at `X`. The map $\theta_P$ is `J.toPlus P`, and `J.plusFunctor D` is the functor $P \mapsto P^+$. The file proves `isIso_toPlus_of_isSheaf` and the universal property `plusLift`, `toPlus_plusLift` and `plusLift_unique`.

<?decl CategoryTheory.GrothendieckTopology.plusObj?>
:::

### Theorems and proofs

The proofs are for presheaves of sets. The first lemma computes the restriction of a class to the morphisms of its sieve.

**Lemma.** Let $[S, x] \in P^+(X)$ and let $f : Y \to X$ be in $S$. Then $[S, x]|_f = \theta_P(x_f)$.

*Proof.* Since $f$ is in $S$, $f^* S = \top$. For each $g$ with target $Y$, the compatibility of $x$ gives $(f^* x)_g = x_{f \circ g} = x_f|_g$. So $[S, x]|_f = [\top, (x_f|_g)_g] = \theta_P(x_f)$. $\square$

**Theorem (The plus construction of a sheaf).** If $P$ is a sheaf, then $\theta_P$ is an isomorphism.

*Proof.* For each covering sieve $S$, the amalgamation gives a bijection $\mathrm{Match}(S, P) \cong P(X)$, and for $R \subseteq S$ the restriction of families corresponds to the identity of $P(X)$. So the diagram is isomorphic to the constant diagram with value $P(X)$, and its colimit is $P(X)$. The map $\theta_P$ is the inclusion of the term at $\top$, so it is a bijection. $\square$

**Theorem (Separation).** For each presheaf $P$, the presheaf $P^+$ is separated. If $P$ is separated, then $\theta_P$ is injective.

*Proof.* Let $u = [S_x, x]$ and $v = [S_y, y]$ be in $P^+(X)$, let $S$ be a covering sieve, and let $u|_f = v|_f$ for each $f$ in $S$. For $f : Y \to X$ in $S$, the equality $u|_f = v|_f$ gives a covering sieve $R_f$ on $Y$ with $R_f \subseteq f^* S_x \cap f^* S_y$ and $x_{f \circ g} = y_{f \circ g}$ for $g$ in $R_f$. Let $B$ be the sieve of composites $f \circ g$ with $f$ in $S$ and $g$ in $R_f$. By the theorem on composite covers in Section 1, $B$ is covering. Also $B \subseteq S_x \cap S_y$, and $x$ and $y$ agree on $B$. So $u = v$.

Now let $P$ be separated, and let $\theta_P(s) = \theta_P(t)$. Then there is a covering sieve $R$ with $s|_f = t|_f$ for each $f$ in $R$, and $s = t$ because $P$ is separated for $R$. $\square$

**Theorem (The plus construction of a separated presheaf).** If $P$ is separated, then $P^+$ is a sheaf. So $P^{++}$ is a sheaf for each presheaf $P$.

*Proof.* By the previous theorem, $P^+$ is separated, so only the existence of amalgamations is necessary. Let $S$ be a covering sieve on $X$ and let $(z_f)_{f \in S}$ be a compatible family of $P^+$ for $S$. For each $f : Y_f \to X$ in $S$, choose $z_f = [T_f, w^f]$ with $T_f \in J(Y_f)$ and $w^f \in \mathrm{Match}(T_f, P)$.

Let $B$ be the covering sieve of the composites $f \circ g$ with $f$ in $S$ and $g$ in $T_f$. Put $w_{f \circ g} = w^f_g$. This does not depend on the choice of $f$ and $g$. If $f \circ g = f' \circ g'$ with source $Z$, the compatibility of $z$ gives $z_f|_g = z_{f'}|_{g'}$ in $P^+(Z)$. By the lemma, $z_f|_g = \theta_P(w^f_g)$ and $z_{f'}|_{g'} = \theta_P(w^{f'}_{g'})$. Since $\theta_P$ is injective, $w^f_g = w^{f'}_{g'}$.

The family $w$ is compatible, because $w_{f \circ g \circ k} = w^f_{g \circ k} = w^f_g|_k$. Let $t = [B, w] \in P^+(X)$. For $f$ in $S$, the restriction $t|_f$ is the class of the family $g \mapsto w_{f \circ g}$ on $f^* B$. The sieve $T_f$ is inside $f^* B$, and on $T_f$ this family is $w^f$. So $t|_f = [T_f, w^f] = z_f$, and $t$ is an amalgamation.

For the last statement, $P^+$ is separated for each $P$, so $(P^+)^+$ is a sheaf. $\square$

**Theorem (Sheafification is a left adjoint).** Let $F$ be a sheaf and let $\varphi : P \to F$. Then there is exactly one morphism $\bar\varphi : aP \to F$ with $\bar\varphi \circ \eta_P = \varphi$. Thus $P \mapsto aP$ is a left adjoint to the inclusion of sheaves into presheaves, with unit $\eta$.

*Proof.* It is enough to prove the statement for one plus construction, and to use it two times. The plus construction is a functor, and $\theta$ is natural, so $\varphi^+ \circ \theta_P = \theta_F \circ \varphi$. Since $F$ is a sheaf, $\theta_F$ is an isomorphism, and $\theta_F^{-1} \circ \varphi^+$ is a morphism $P^+ \to F$ through which $\varphi$ factors.

For the uniqueness, let $\alpha, \beta : P^+ \to F$ with $\alpha \circ \theta_P = \beta \circ \theta_P$, and let $u = [S, x] \in P^+(X)$. For $f$ in $S$, the lemma gives $u|_f = \theta_P(x_f)$. So $\alpha(u)|_f = \alpha(\theta_P(x_f)) = \beta(\theta_P(x_f)) = \beta(u)|_f$. Since $F$ is separated, $\alpha(u) = \beta(u)$. $\square$

**Theorem (Left exactness).** The functor $P \mapsto P^+$ on presheaves of sets preserves finite limits. So sheafification preserves finite limits.

*Proof.* Limits of presheaves are computed objectwise. The functor $P \mapsto \mathrm{Match}(S, P)$ is a limit construction, so it preserves all limits. The colimit over $J(X)$ is filtered, and in sets filtered colimits commute with finite limits (Volume 24, Chapter 4). So $P \mapsto P^+(X)$ preserves finite limits, and so does the composite $P \mapsto P^{++}$. $\square$

The same proofs hold for presheaves with values in a category $D$ of algebraic structures, such as groups, abelian groups, rings and modules. The forgetful functor to sets must preserve limits and filtered colimits and reflect isomorphisms. Then the underlying set of $P^+(X)$ is the plus construction of the underlying presheaf of sets, and Section 2 shows that a presheaf is a sheaf if and only if its underlying presheaf of sets is a sheaf.

**Theorem (Sheaves in an abelian category).** Let $D$ be abelian and let $J$ have a sheafification for $D$ that preserves finite limits. Then the category of sheaves with values in $D$ is abelian, and sheafification is an additive functor.

*Proof (outline).* The presheaves with values in $D$ form an abelian category, with kernels and cokernels computed objectwise. The sheaves are a full subcategory that is closed under limits, so the kernel of a morphism of sheaves is the kernel in presheaves. The cokernel of a morphism of sheaves is the sheafification of the cokernel in presheaves, because sheafification is a left adjoint. The reflector preserves finite limits and finite colimits, so it is exact. A general result on such reflective subcategories of an abelian category then gives the axioms of Chapter 2. $\square$

### Examples

**Example (The constant presheaf).** Let $T$ be a space with the topology of open covers, let $A$ be a set with at least two elements, and let $P(U) = A$ for each open $U$, with identity restrictions. The plus construction must be applied two times.

First, $P$ is not separated. The empty sieve covers $\emptyset$, and each element of $A$ is an amalgamation of the empty family. Compute $P^+$. If $U$ is nonempty, each covering sieve $S$ on $U$ contains the empty open set, and the compatibility of a family $x$ for the pair $V \supseteq \emptyset \subseteq W$ gives $x_V = x_W$. So $\mathrm{Match}(S, P) = A$, and $P^+(U) = A$. Also $P^+(\emptyset)$ is a point, because the empty sieve gives one empty family. Thus $P^+$ is the presheaf of constant functions to $A$.

The presheaf $P^+$ is separated but not a sheaf. Section 2 shows this for two disjoint nonempty open sets. The second plus construction gives $P^{++}(U)$ as the set of locally constant functions $U \to A$. A class $[S, x]$ is a family of constant functions on the members of $S$ that agree on the intersections, and such a family is one locally constant function on $U$.

**Example (A cokernel in sheaves).** Let $X = \mathbb{C} \setminus \{0\}$. Let $F(U)$ be the additive group of continuous functions $U \to \mathbb{C}$ and $G(U)$ the multiplicative group of continuous functions $U \to \mathbb{C}^\times$. The map $\exp : F \to G$ is a morphism of sheaves of abelian groups. Its cokernel in presheaves is not zero at $X$, because the function $z \mapsto z$ has no continuous logarithm on $X$. Each point has a disc around it on which each continuous function to $\mathbb{C}^\times$ has a continuous logarithm. So each section of the presheaf cokernel is locally zero, and the sheafification of the cokernel is zero. Thus $\exp$ is an epimorphism of sheaves, but the map $F(X) \to G(X)$ is not surjective. So the functor of sections at $X$ does not preserve epimorphisms. Volume 26 measures this failure with sheaf cohomology.

**Example (The trivial topology).** For the trivial topology, each presheaf is a sheaf, and sheafification is the identity functor. Mathlib has this as an instance of `HasSheafify` for `⊥`.

**Example (Sheaves of types).** The category of sheaves of types on any site is balanced, finitary extensive and adhesive. These properties come from the same properties of presheaves, because sheafification preserves finite limits and the colimits of sheaves are sheafifications of colimits of presheaves. Chapter 7 defines extensive and adhesive categories.

### The library around it

::: mathlib
`CategoryTheory.HasSheafify` · `Mathlib.CategoryTheory.Sites.Sheafification`

`HasWeakSheafify J A` is the statement that `sheafToPresheaf J A` is a right adjoint. The class `HasSheafify J A` adds that the left adjoint preserves finite limits. With these classes, `presheafToSheaf J A` is the left adjoint, `sheafificationAdjunction J A` is the adjunction, and `sheafify J P` and `toSheafify J P` are the presheaf $aP$ and the unit. The lemmas `sheafifyLift`, `toSheafify_sheafifyLift` and `sheafifyLift_unique` give the universal property.

<?decl CategoryTheory.HasSheafify?>
:::

::: mathlib
`CategoryTheory.GrothendieckTopology.Plus.isSheaf_plus_plus` · `Mathlib.CategoryTheory.Sites.ConcreteSheafification`

For a concrete category `D` with the necessary limits and colimits, the file proves `Plus.sep`, `Plus.inj_of_sep` and `Plus.isSheaf_of_sep`, then `isSheaf_plus_plus`. Then `J.sheafify P` is `J.plusObj (J.plusObj P)`, and `plusPlusAdjunction J D` is the adjunction. The type `Meq P S` is the type of compatible families on a cover, as elements of the underlying types.

<?decl CategoryTheory.GrothendieckTopology.Plus.isSheaf_plus_plus?>
:::

::: mathlib
`CategoryTheory.sheafIsAbelian` · `Mathlib.CategoryTheory.Sites.Abelian`

The instance needs `[Abelian D]` and `[HasSheafify J D]`. The file also gives `presheafToSheaf_additive`. The file `Sites.LeftExact` gives `HasSheafify J D` for concrete categories whose forgetful functor preserves limits and filtered colimits, with a smallness condition on the covers, and it proves `preservesFiniteLimits_presheafToSheaf`.

<?decl CategoryTheory.sheafIsAbelian?>
:::

The isomorphism `plusPlusSheafIsoPresheafToSheaf` compares the plus construction with the left adjoint that the classes give.

Common errors of a learner:

- `J.sheafify P` is the plus construction applied two times, from `ConcreteSheafification`. `sheafify J P` is the presheaf of the left adjoint, from `Sheafification`. They are isomorphic by `plusPlusIsoSheafify`, but they are not equal.
- `HasWeakSheafify` gives the adjunction only. The statement that sheafification preserves finite limits needs `HasSheafify`.
- The instances for types need universe conditions. For `C : Type u` with morphisms in `Type v`, Mathlib gives `HasSheafify J (Type (max u v))`.
- A monomorphism of sheaves is a monomorphism of presheaves, but an epimorphism of sheaves need not be an epimorphism of presheaves, as the example of the exponential shows.

### Exercises

1. (A) Show that $\theta_P$ is natural in $P$: for $\varphi : P \to Q$, $\varphi^+ \circ \theta_P = \theta_Q \circ \varphi$.
2. (A) For the trivial topology, show that $\theta_P$ is an isomorphism for each $P$.
3. (B) In the example of the constant presheaf, show that $P^+$ is not a sheaf when $T$ has two disjoint nonempty open sets, and give the bijection between $P^{++}(U)$ and the locally constant functions $U \to A$.
4. (B) Show directly that sheafification of presheaves of sets preserves the terminal object and binary products.
5. (B) Let $\varphi : F \to G$ be a morphism of sheaves of abelian groups. Show that the presheaf kernel of $\varphi$ is a sheaf, and that the presheaf image of $\varphi$ need not be a sheaf.
6. (C) Let $\varphi : F \to G$ be a morphism of sheaves of sets. Suppose that for each $t \in G(X)$ there is a covering sieve $S$ with $t|_f$ in the image of $\varphi$ for each $f$ in $S$. Show that $\varphi$ is an epimorphism in the category of sheaves.
7. (C) In the example of the exponential, prove that the sheafification of the presheaf cokernel is zero, and that its value at $X$ before sheafification is not zero.

### Notes and history

For sheaves on a space, the sheafification is in the book of Godement, *Topologie algébrique et théorie des faisceaux* (1958), as the sheaf of continuous sections of the étalé space. The plus construction for a site is due to Grothendieck and is in Exposé II of SGA 4. The source files follow the Stacks project, tag 00W1. The exactness of sheafification is the key step in the proof that the sheaves on a site form a Grothendieck topos, and in the proof that the sheaves of abelian groups have enough injectives, which Volume 26 uses for sheaf cohomology.

The Mathlib Authors line of `Sites.Plus`, `Sites.ConcreteSheafification` and `Sites.LeftExact` names Adam Topaz. The file `Sites.Sheafification` is by Dagur Asgeirsson, and `Sites.Abelian` is by Adam Topaz and Jujian Zhang.

### Reference

<?reference?>
