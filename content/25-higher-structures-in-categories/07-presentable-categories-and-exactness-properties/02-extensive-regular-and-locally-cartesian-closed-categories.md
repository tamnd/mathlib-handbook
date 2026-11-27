---
title: Extensive, regular and locally cartesian closed categories
kind: theory
modules:
  - Mathlib.CategoryTheory.Extensive
  - Mathlib.CategoryTheory.Adhesive.Basic
  - Mathlib.CategoryTheory.Distributive.Cartesian
  - Mathlib.CategoryTheory.RegularCategory.Basic
  - Mathlib.CategoryTheory.LocallyCartesianClosed.ExponentiableMorphism
  - Mathlib.CategoryTheory.LocallyCartesianClosed.Over
  - Mathlib.CategoryTheory.Sites.Closed
  - Mathlib.CategoryTheory.Topos.Sheaf
explains:
  E3: [CategoryTheory.FinitaryExtensive, CategoryTheory.Adhesive, CategoryTheory.IsCartesianDistributive, CategoryTheory.Regular, CategoryTheory.Regular.strongEpiMonoFactorisation, CategoryTheory.ExponentiableMorphism, CategoryTheory.Presheaf.classifier, CategoryTheory.Sheaf.classifier]
  E2: [CategoryTheory.FinitaryPreExtensive, CategoryTheory.HasPullbacksOfInclusions, CategoryTheory.FinitaryExtensive.vanKampen, CategoryTheory.FinitaryExtensive.mono_inl_of_isColimit, CategoryTheory.FinitaryExtensive.isPullback_initial_to_binaryCofan, CategoryTheory.hasStrictInitialObjects_of_finitaryPreExtensive, CategoryTheory.FinitaryExtensive.isVanKampen_finiteCoproducts, CategoryTheory.types.finitaryExtensive, CategoryTheory.finitaryExtensive_TopCat, CategoryTheory.finitaryExtensive_functor, CategoryTheory.finitaryExtensive_of_reflective, CategoryTheory.IsPushout.IsVanKampen, CategoryTheory.Type.adhesive, CategoryTheory.adhesive_functor, CategoryTheory.adhesive_of_reflective, CategoryTheory.Adhesive.toRegularMonoCategory, CategoryTheory.Adhesive.mono_of_isPushout_of_mono_left, CategoryTheory.Adhesive.isPullback_of_isPushout_of_mono_left, CategoryTheory.IsCartesianDistributive.monoCoprod, CategoryTheory.IsCartesianDistributive.of_isMonoidalLeftDistrib, CategoryTheory.Regular.hasCoequalizer_of_isKernelPair, CategoryTheory.Regular.regularEpiIsStableUnderBaseChange, CategoryTheory.Regular.hasStrongEpiMonoFactorisations, CategoryTheory.Regular.isRegularEpi_of_extremalEpi, CategoryTheory.Regular.exists_inf_pullback_eq_exists_inf, CategoryTheory.ExponentiableMorphism.pushforward, CategoryTheory.ExponentiableMorphism.pullbackPushforwardAdj, CategoryTheory.IsExponentiable, CategoryTheory.ExponentiableMorphism.id, CategoryTheory.ExponentiableMorphism.comp, CategoryTheory.ExponentiableMorphism.ev, CategoryTheory.ExponentiableMorphism.coev, CategoryTheory.toOver, CategoryTheory.forgetAdjToOver, CategoryTheory.equivToOverUnit, CategoryTheory.GrothendieckTopology.IsClosed, CategoryTheory.GrothendieckTopology.close, CategoryTheory.Functor.sieves, CategoryTheory.Functor.closedSieves, CategoryTheory.classifier_isSheaf, CategoryTheory.Presheaf.truth, CategoryTheory.Presheaf.χ, CategoryTheory.Presheaf.isPullback_χ_truth, CategoryTheory.Presheaf.χ_unique, CategoryTheory.Sheaf.Ω, CategoryTheory.Sheaf.truth, CategoryTheory.Sheaf.χ, CategoryTheory.Sheaf.χ_unique]
  E1: auto
families: []
requires: [V24.C04, V24.C05, V24.C07, V25.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Extensive, regular and locally cartesian closed categories

### Overview

The category of sets has many good properties that a general category does not have. Coproducts are disjoint unions, and they are stable under pullback. Each map is a surjection followed by an injection, and surjections are stable under pullback. Each map $f : I \to J$ gives a functor of dependent products from sets over $I$ to sets over $J$. A subset of $X$ is the same as a map from $X$ to a set with two elements. Each of these properties becomes an axiom on a category. The axioms are exactness properties, and a category of sheaves on a site has all of them.

This section defines extensive and adhesive categories, distributive categories, regular categories, exponentiable morphisms and subobject classifiers. It proves the main first consequences of each axiom, and it constructs the subobject classifier of a category of presheaves and of a category of sheaves.

In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`. For an object $J$, the category $C/J$ is the category of objects over $J$ of Volume 24, Chapter 5. For $f : I \to J$, the functor $f^* : C/J \to C/I$ is the pullback along $f$.

### Definitions

**Definition (Extensive category).** Let $C$ have finite coproducts and pullbacks along coproduct injections. Then $C$ is extensive if the binary coproducts are van Kampen colimits in this sense. Let $p : Z \to X \sqcup Y$, and let a commutative diagram

$$\begin{array}{ccccc} X' & \xrightarrow{a} & Z & \xleftarrow{b} & Y' \\ \downarrow & & \downarrow p & & \downarrow \\ X & \xrightarrow{\iota_1} & X \sqcup Y & \xleftarrow{\iota_2} & Y \end{array}$$

be given. Then $(Z, a, b)$ is a coproduct of $X'$ and $Y'$ if and only if the two squares are pullbacks. The category is pre-extensive if the "if" direction is true. In that case the coproducts are universal: a pullback of a coproduct is a coproduct.

**Definition (Strict initial object).** An initial object $0$ is strict if each morphism $X \to 0$ is an isomorphism.

**Definition (Adhesive category).** A category $C$ is adhesive if it has pullbacks along monomorphisms and pushouts along monomorphisms, and each pushout of a monomorphism is van Kampen. A pushout square $Z = X \sqcup_W Y$ is van Kampen if for each commutative cube on it, whose two back faces are pullbacks, the top face is a pushout if and only if the two front faces are pullbacks.

**Definition (Distributive category).** A category with finite products and binary coproducts is cartesian distributive if the canonical morphisms

$$(X \times Y) \sqcup (X \times Z) \to X \times (Y \sqcup Z), \qquad (Y \times X) \sqcup (Z \times X) \to (Y \sqcup Z) \times X$$

are isomorphisms.

**Definition (Regular category).** A category $C$ is regular if it has finite limits, the kernel pair of each morphism has a coequalizer, and the regular epimorphisms are stable under pullback. The kernel pair of $f : X \to Y$ is the pair of projections $p_1, p_2 : X \times_Y X \to X$.

**Definition (Exponentiable morphism).** A morphism $f : I \to J$ with pullbacks along $f$ is exponentiable if $f^* : C/J \to C/I$ has a right adjoint $\Pi_f$, the pushforward along $f$. A category with pullbacks is locally cartesian closed if each morphism is exponentiable.

**Definition (Subobject classifier).** A subobject classifier of $C$ is a monomorphism $\top : \Omega_0 \to \Omega$ with this property. For each monomorphism $m : U \to X$ there is exactly one morphism $\chi_m : X \to \Omega$ such that $m$ is a pullback of $\top$ along $\chi_m$. In the usual case $\Omega_0$ is a terminal object.

::: mathlib
`CategoryTheory.FinitaryExtensive` · `Mathlib.CategoryTheory.Extensive`

The class has the fields `hasFiniteCoproducts`, `hasPullbacksOfInclusions` and `van_kampen'`. The last field says that each colimit binary cofan is an `IsVanKampenColimit`. The class `FinitaryPreExtensive` asks only for `IsUniversalColimit`. The lemma `FinitaryExtensive.isVanKampen_finiteCoproducts` extends the property to all finite coproducts.

<?decl CategoryTheory.FinitaryExtensive?>
:::

### Theorems and proofs

**Theorem (Disjoint coproducts).** In an extensive category, the coproduct injections are monomorphisms, and the pullback of $\iota_1$ and $\iota_2$ is an initial object.

*Proof.* Apply the definition with $p = \iota_1 : X \to X \sqcup Y$, $X' = X$, $Y' = 0$, $a = 1_X$ and $b$ the morphism $0 \to X$. The left vertical morphism is $1_X$, and the right one is $0 \to Y$. The left square commutes. The right square commutes because its two composites are morphisms out of $0$. The object $X$ with $1_X$ and $0 \to X$ is a coproduct of $X$ and $0$. So the two squares are pullbacks. The left square says that $X$ with $1_X$ and $1_X$ is a pullback of $\iota_1$ along $\iota_1$, so $\iota_1$ is a monomorphism. The right square says that $0$ is a pullback of $\iota_1$ and $\iota_2$. The argument for $\iota_2$ is symmetric. $\square$

**Theorem (Strict initial object).** In a pre-extensive category, the initial object is strict.

*Proof.* The object $0$ with $1_0$ and $1_0$ is a coproduct of $0$ and $0$, because two morphisms out of $0$ are equal. Let $f : X \to 0$. The pullback of $1_0$ along $f$ is $X$ with $1_X$. The coproducts are universal, so $X$ with $1_X$ and $1_X$ is a coproduct of $X$ and $X$. Thus for each two morphisms $g, h : X \to W$, there is $u : X \to W$ with $u = g$ and $u = h$. So there is at most one morphism from $X$ to each object. Let $z : 0 \to X$ be the unique morphism. Then $f \circ z = 1_0$, and $z \circ f = 1_X$ because both are morphisms out of $X$. So $f$ is an isomorphism. $\square$

**Theorem (Sets are extensive).** The category of sets is extensive.

*Proof.* Let $p : Z \to X \sqcup Y$, and let $Z_X = p^{-1}(X)$ and $Z_Y = p^{-1}(Y)$. The sets $Z_X$ and $Z_Y$ are disjoint, and their union is $Z$. The injection $\iota_1$ is injective, so the pullback of $\iota_1$ and $p$ is $Z_X$, and the left square is a pullback if and only if $a$ is a bijection from $X'$ to $Z_X$. Similarly, the right square is a pullback if and only if $b$ is a bijection from $Y'$ to $Z_Y$. The images of $a$ and $b$ are in $Z_X$ and in $Z_Y$, by the commutativity of the squares. So the map $X' \sqcup Y' \to Z$ given by $a$ and $b$ is bijective if and only if $a$ and $b$ are bijections onto $Z_X$ and $Z_Y$. $\square$

**Theorem (Adhesive pushouts).** In an adhesive category, let $Z = X \sqcup_W Y$ be the pushout of a monomorphism $m : W \to X$ and a morphism $g : W \to Y$, with $h : X \to Z$ and $i : Y \to Z$. Then the square is a pullback, and $i$ is a monomorphism.

*Proof.* Make a cube with the pushout as the bottom face. The top face is the square with $W \xrightarrow{1} W$, $W \xrightarrow{g} Y$, $W \xrightarrow{g} Y$ and $Y \xrightarrow{1} Y$. It is a pushout. The vertical morphisms are $1_W$, $m : W \to X$, $1_Y$ and $i : Y \to Z$. The cube commutes, because $i \circ g = h \circ m$. The back face over $m$ is the square with $1_W$, $1_W$, $m$ and $m$. It is a pullback because $m$ is a monomorphism. The back face over $g$ has two identity sides, so it is a pullback. The pushout is van Kampen and the top face is a pushout, so the two front faces are pullbacks. The front face over $h$ has the sides $g$, $m$, $i$ and $h$, so the original square is a pullback. The front face over $i$ has the sides $1_Y$, $1_Y$, $i$ and $i$, so $i$ is a monomorphism. $\square$

**Theorem (Injections in a distributive category).** In a cartesian distributive category, the coproduct injections are monomorphisms.

*Proof.* Let $\delta : (X \times X) \sqcup (X \times Y) \to X \times (X \sqcup Y)$ be the canonical isomorphism. On the first summand $\delta$ is $1 \times \iota_1$. Let $r : (X \times X) \sqcup (X \times Y) \to X$ be the second projection on the first summand and the first projection on the second summand. For $c : W \to X$ and $a : W \to X$, the morphism $\langle a, \iota_1 \circ c \rangle$ is $(1 \times \iota_1) \circ \langle a, c \rangle = \delta \circ \iota_1 \circ \langle a, c \rangle$. So $r \circ \delta^{-1} \circ \langle a, \iota_1 \circ c \rangle = c$. Now let $\iota_1 \circ a = \iota_1 \circ b$. Then $\langle a, \iota_1 \circ a \rangle = \langle a, \iota_1 \circ b \rangle$. Apply $r \circ \delta^{-1}$ to the two sides, and the result is $a = b$. $\square$

An extensive category with finite products is distributive. The coproduct $Y \sqcup Z$ pulls back along the projection $X \times (Y \sqcup Z) \to Y \sqcup Z$ to the coproduct of $X \times Y$ and $X \times Z$, because the coproducts are universal. The index of this edition has no declaration for this implication. A cartesian closed category is distributive, because $X \times -$ is a left adjoint and so it preserves coproducts.

**Theorem (Factorization in a regular category).** In a regular category, each morphism $f : X \to Y$ is $m \circ e$, where $e$ is the coequalizer of the kernel pair of $f$ and $m$ is a monomorphism.

*Proof.* Let $p_1, p_2$ be the kernel pair of $f$ and let $e : X \to I$ be their coequalizer. Then $f \circ p_1 = f \circ p_2$, so $f = m \circ e$ for a unique $m : I \to Y$. Let $q_1, q_2 : I \times_Y I \to I$ be the kernel pair of $m$. The morphism $e \times_Y e : X \times_Y X \to I \times_Y I$ is the composite of $e \times_Y 1 : X \times_Y X \to I \times_Y X$ and $1 \times_Y e : I \times_Y X \to I \times_Y I$. A check with the pasting lemma for pullbacks shows that each of the two factors is a pullback of $e$. So each factor is a regular epimorphism, and in particular an epimorphism. Thus $e \times_Y e$ is an epimorphism. Now $q_1 \circ (e \times_Y e) = e \circ p_1$ and $q_2 \circ (e \times_Y e) = e \circ p_2$. These are equal because $e$ coequalizes $p_1$ and $p_2$. So $q_1 = q_2$. A morphism with equal kernel pair projections is a monomorphism, so $m$ is a monomorphism. $\square$

The factorization is a strong epi-mono factorization, because a regular epimorphism is strong. Mathlib also proves the Frobenius law $\exists_f(A \wedge f^* B) = \exists_f A \wedge B$ for subobjects $A$ of $X$ and $B$ of $Y$, where $\exists_f A$ is the image of $A$ in $Y$.

**Theorem (Dependent products of sets).** In the category of sets, each map $f : I \to J$ is exponentiable. For $A \to I$ with fibers $A_i$, the pushforward $\Pi_f A$ has the fiber $\prod_{i \in f^{-1}(j)} A_i$ over $j$.

*Proof.* For $B \to J$ with fibers $B_j$, the pullback $f^* B$ has the fiber $B_{f(i)}$ over $i$. A morphism $f^* B \to A$ over $I$ is a family of maps $B_{f(i)} \to A_i$ for $i \in I$. Group the indices $i$ by $j = f(i)$. Such a family is a family, over $j \in J$, of families of maps $B_j \to A_i$ with $i \in f^{-1}(j)$. A family of maps $B_j \to A_i$ is a map $B_j \to \prod_{i \in f^{-1}(j)} A_i$. So morphisms $f^* B \to A$ over $I$ correspond to morphisms $B \to \Pi_f A$ over $J$. Each step is natural in $A$ and $B$. $\square$

**Theorem (Classifier of presheaves).** Let $C$ be a category, and let $\Omega(X)$ be the set of sieves on $X$, with $\Omega(g)(S) = g^* S$. Let $\top$ pick the maximal sieve. For a subpresheaf $m : F \to G$ and $x \in G(X)$, put

$$\chi_m(x) = \{ f : Y \to X \mid x|_f \in F(Y) \}.$$

Then $\top : 1 \to \Omega$ is a subobject classifier of the presheaves of sets on $C$.

*Proof.* If $f$ is in $\chi_m(x)$ and $g : Z \to Y$, then $x|_{f \circ g} = (x|_f)|_g$ is in $F(Z)$. So $\chi_m(x)$ is a sieve. For $g : X' \to X$, a morphism $f$ is in $\chi_m(x|_g)$ if and only if $x|_{g \circ f} \in F$, that is, if and only if $f \in g^* \chi_m(x)$. So $\chi_m$ is natural. The sieve $\chi_m(x)$ is maximal if and only if $1_X \in \chi_m(x)$, that is, if and only if $x \in F(X)$. Pullbacks of presheaves are computed objectwise, so $F$ is the pullback of $\top$ along $\chi_m$. For uniqueness, let $\varphi : G \to \Omega$ have the same pullback. By Chapter 6, Section 1, a morphism $f$ is in a sieve $S$ if and only if $f^* S$ is maximal. So $f \in \varphi(x)$ if and only if $\varphi(x|_f)$ is maximal, that is, if and only if $x|_f \in F(Y)$. Thus $\varphi(x) = \chi_m(x)$. $\square$

**Theorem (Classifier of sheaves).** Let $J$ be a Grothendieck topology on $C$. A sieve $S$ on $X$ is $J$-closed if each $f : Y \to X$ with $f^* S \in J(Y)$ is in $S$. The closed sieves form a sheaf $\Omega_J$, and the maximal sieve $\top : 1 \to \Omega_J$ is a subobject classifier of $\mathrm{Sheaf}(C, J)$.

*Proof (outline).* The proof that $\Omega_J$ is a sheaf follows Mac Lane and Moerdijk, Chapter III, Section 7. Let $m : F \to G$ be a monomorphism of sheaves, and $x \in G(X)$. The sieve $\chi_m(x)$ is closed. Let $f : Y \to X$ with $R = f^* \chi_m(x)$ covering. For each $g$ in $R$, the element $x|_{f \circ g}$ is in $F$. These elements are a compatible family of $F$ for $R$, so they have an amalgamation $y$ in $F(Y)$. The elements $y$ and $x|_f$ of $G(Y)$ have the same restrictions along $R$, so they are equal because $G$ is a sheaf. Thus $f \in \chi_m(x)$. The rest of the proof is the proof for presheaves. $\square$

### Examples

**Example (Categories of spaces).** The category of topological spaces is extensive. A continuous map $p : Z \to X \sqcup Y$ gives the open and closed sets $p^{-1}(X)$ and $p^{-1}(Y)$, and $Z$ is their disjoint union as a space. The category of topological spaces is not regular, because a pullback of a quotient map need not be a quotient map.

**Example (Functor categories).** If $D$ is extensive and has pullbacks, then each functor category $C \to D$ is extensive, because colimits and pullbacks are computed objectwise. The same is true for adhesive categories. Thus categories of presheaves of sets are extensive and adhesive. A reflective subcategory with a left adjoint that preserves the relevant pullbacks inherits these properties. So the category of sheaves of sets on a site is extensive and adhesive, as Chapter 6, Section 3 notes.

**Example (Rings).** The category of commutative rings is not extensive. Its initial object $\mathbb{Z}$ is not strict, because there is a morphism $\mathbb{Z} \to 0$ to the zero ring, and the zero ring is not isomorphic to $\mathbb{Z}$. The opposite category, the category of affine schemes, is extensive.

**Example (Regular categories).** The category of sets is regular, because the regular epimorphisms are the surjections, and a pullback of a surjection is a surjection. Each abelian category is regular, because each epimorphism is a cokernel, and a pullback of an epimorphism is an epimorphism in an abelian category. The index of this edition has no instance of `Regular` for these categories.

**Example (Slices over a product).** In a category with finite products, the functor $\mathrm{Over}(X) \to C$ that forgets the morphism to $X$ is left adjoint to the functor $A \mapsto (A \times X \to X)$. A morphism $Z \to A$ is the same as a morphism $Z \to A \times X$ over $X$. For the terminal object $1$, the category $C/1$ is equivalent to $C$.

### The library around it

::: mathlib
`CategoryTheory.Adhesive` · `Mathlib.CategoryTheory.Adhesive.Basic`

The class has instance fields for the pullbacks and pushouts along monomorphisms, and the field `van_kampen`, which says that each pushout of a monomorphism satisfies `IsPushout.IsVanKampen`. The instances `Type.adhesive` and `Adhesive.toRegularMonoCategory` give the adhesive structure of `Type u` and the regularity of monomorphisms. The lemmas `Adhesive.isPullback_of_isPushout_of_mono_left` and `Adhesive.mono_of_isPushout_of_mono_left` are the theorem on adhesive pushouts.

<?decl CategoryTheory.Adhesive?>
:::

::: mathlib
`CategoryTheory.Regular` · `Mathlib.CategoryTheory.RegularCategory.Basic`

The class extends `HasFiniteLimits C` with the fields `hasCoequalizer_of_isKernelPair` and `regularEpiIsStableUnderBaseChange`. The definition `Regular.strongEpiMonoFactorisation f` is the factorization of the theorem, and `Regular.hasStrongEpiMonoFactorisations` is the instance. The theorem `Regular.exists_inf_pullback_eq_exists_inf` is the Frobenius law.

<?decl CategoryTheory.Regular?>
:::

::: mathlib
`CategoryTheory.ExponentiableMorphism` · `Mathlib.CategoryTheory.LocallyCartesianClosed.ExponentiableMorphism`

For `f : I ⟶ J` with `[ChosenPullbacksAlong f]`, the class has the fields `pushforward : Over I ⥤ Over J` and `pullbackPushforwardAdj f : pullback f ⊣ pushforward`. The definitions `ExponentiableMorphism.id` and `ExponentiableMorphism.comp` give the identity and the composite. The property `IsExponentiable` asks only that `pullback f` is a left adjoint.

<?decl CategoryTheory.ExponentiableMorphism?>
:::

::: mathlib
`CategoryTheory.Sheaf.classifier` · `Mathlib.CategoryTheory.Topos.Sheaf`

For `J : GrothendieckTopology C`, the definition is a `Subobject.Classifier (Sheaf J (Type max u v))`. Its object is `Sheaf.Ω J`, the sheaf of `Functor.closedSieves J`. The theorem `classifier_isSheaf` in `Mathlib.CategoryTheory.Sites.Closed` proves the sheaf condition. The presheaf case is `Presheaf.classifier`, with `Presheaf.χ` and `Presheaf.χ_unique`.

<?decl CategoryTheory.Sheaf.classifier?>
:::

The class `IsCartesianDistributive C` is the abbreviation `IsMonoidalDistrib C` for the cartesian monoidal structure. The lemma `IsCartesianDistributive.of_isMonoidalLeftDistrib` shows that the left distributive law is enough, and the instance `IsCartesianDistributive.monoCoprod` is the theorem on injections. The functor `toOver X` and the adjunction `forgetAdjToOver X` are the example of slices over a product, and `equivToOverUnit` is the equivalence $C/1 \simeq C$.

Common errors of a learner:

- `FinitaryExtensive` is about finite coproducts only. Mathlib has no class for infinitary extensive categories in this edition.
- `IsPushout.IsVanKampen` is a property of a pushout square, but `IsVanKampenColimit` is a property of a colimit cocone in `Mathlib.CategoryTheory.Limits.VanKampen`. The two notions agree for pushouts, by `IsPushout.isVanKampen_iff`.
- `ExponentiableMorphism f` needs the instance `ChosenPullbacksAlong f`. The pullback functor is built from these chosen pullbacks, not from `HasPullbacks`.
- The classifier of sheaves is for sheaves with values in `Type (max u v)`, where `C : Type u` and the morphisms of `C` are in `Type v`.

### Exercises

1. (A) Show that in an extensive category, the coproduct of two morphisms $X \to X'$ and $Y \to Y'$ is a monomorphism if both are monomorphisms.
2. (A) Show that a category with a strict initial object $0$ has at most one morphism from $X$ to each object when there is a morphism $X \to 0$.
3. (A) In the category of sets, describe the kernel pair of a map $f$ and its coequalizer, and show that the factorization of the theorem is the factorization through the image.
4. (B) Show that the category of pointed sets is not extensive. *Hint:* the initial object is the one-point set, and it is not strict.
5. (B) Show that the identity of $I$ is exponentiable, with $\Pi_{1_I}$ the identity functor, and that the composite of two exponentiable morphisms is exponentiable, with $\Pi_{g \circ f} \cong \Pi_g \circ \Pi_f$.
6. (B) For a topological space $T$ and the topology of open covers, show that a sieve $S$ on an open set $U$ is closed if and only if it is the sieve of the open subsets of some open $V \subseteq U$. Deduce that $\Omega_J(U)$ is the set of open subsets of $U$.
7. (C) Show that in a regular category, a pullback of the image factorization is the image factorization of the pullback.

### Notes and history

Extensive categories in this form are in the paper of Carboni, Lack and Walters, *Introduction to extensive and distributive categories* (1993), which the source files cite. Distributive categories are in the paper of Cockett, *Introduction to distributive categories* (1993). Adhesive categories are due to Lack and Sobociński (2004), as a setting for graph rewriting. Regular categories are due to Barr, in *Exact categories* (1971). The source file for regular categories follows the notes of Gran, *An introduction to regular categories*. The subobject classifier is one of the axioms of an elementary topos, due to Lawvere and Tierney. The sheaf proof follows the book of Mac Lane and Moerdijk, *Sheaves in geometry and logic* (1992).

The Mathlib Authors line of `Extensive` names Andrew Yang, and the line of `Adhesive.Basic` names Andrew Yang and Jack McKoen. The files `Distributive.Cartesian`, `LocallyCartesianClosed.ExponentiableMorphism` and `LocallyCartesianClosed.Over` are by Sina Hazratpour. The file `RegularCategory.Basic` is by Fernando Chu, `Sites.Closed` is by Bhavik Mehta, and `Topos.Sheaf` is by Edward van de Meent.

### Reference

<?reference?>
