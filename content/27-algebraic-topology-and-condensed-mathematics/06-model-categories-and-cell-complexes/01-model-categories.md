---
title: Model categories
kind: theory
modules:
  - Mathlib.AlgebraicTopology.ModelCategory.Basic
  - Mathlib.AlgebraicTopology.ModelCategory.Bifibrant
  - Mathlib.AlgebraicTopology.ModelCategory.BifibrantObjectHomotopy
  - Mathlib.AlgebraicTopology.ModelCategory.BrownLemma
  - Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
  - Mathlib.AlgebraicTopology.ModelCategory.CofibrantObjectHomotopy
  - Mathlib.AlgebraicTopology.ModelCategory.DerivabilityStructureCofibrant
  - Mathlib.AlgebraicTopology.ModelCategory.DerivabilityStructureFibrant
  - Mathlib.AlgebraicTopology.ModelCategory.Cylinder
  - Mathlib.AlgebraicTopology.ModelCategory.FibrantObjectHomotopy
  - Mathlib.AlgebraicTopology.ModelCategory.FundamentalLemma
  - Mathlib.AlgebraicTopology.ModelCategory.Homotopy
  - Mathlib.AlgebraicTopology.ModelCategory.Instances
  - Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
  - Mathlib.AlgebraicTopology.ModelCategory.JoyalTrick
  - Mathlib.AlgebraicTopology.ModelCategory.LeftHomotopy
  - Mathlib.AlgebraicTopology.ModelCategory.Opposite
  - Mathlib.AlgebraicTopology.ModelCategory.Over
  - Mathlib.AlgebraicTopology.ModelCategory.PathObject
  - Mathlib.AlgebraicTopology.ModelCategory.RightHomotopy
  - Mathlib.AlgebraicTopology.ModelCategory.Transport
explains:
  E3: [HomotopicalAlgebra.ModelCategory, HomotopicalAlgebra.CategoryWithWeakEquivalences, HomotopicalAlgebra.CategoryWithFibrations, HomotopicalAlgebra.CategoryWithCofibrations, HomotopicalAlgebra.IsCofibrant, HomotopicalAlgebra.IsFibrant, HomotopicalAlgebra.Cylinder, HomotopicalAlgebra.PathObject, HomotopicalAlgebra.LeftHomotopyRel, HomotopicalAlgebra.RightHomotopyRel, HomotopicalAlgebra.leftHomotopyRel_iff_rightHomotopyRel, HomotopicalAlgebra.CofibrantBrownFactorization, HomotopicalAlgebra.LeftHomotopyClass.postcomp_bijective_of_weakEquivalence, HomotopicalAlgebra.RightHomotopyClass.whitehead, HomotopicalAlgebra.bijective_leftHomotopyClassToHom, HomotopicalAlgebra.BifibrantObject.HoCat]
  E2: [HomotopicalAlgebra.Fibration, HomotopicalAlgebra.Cofibration, HomotopicalAlgebra.WeakEquivalence, HomotopicalAlgebra.trivialFibrations, HomotopicalAlgebra.trivialCofibrations, HomotopicalAlgebra.cofibrations_rlp, HomotopicalAlgebra.fibrations_llp, HomotopicalAlgebra.trivialCofibrations_rlp, HomotopicalAlgebra.trivialFibrations_llp, HomotopicalAlgebra.ModelCategory.mk', HomotopicalAlgebra.ModelCategory.over, HomotopicalAlgebra.ModelCategory.hasLiftingProperty_of_joyalTrick, HomotopicalAlgebra.Precylinder.LeftHomotopy, HomotopicalAlgebra.Cylinder.exists_very_good, HomotopicalAlgebra.Cylinder.symm, HomotopicalAlgebra.Cylinder.trans, HomotopicalAlgebra.PathObject.exists_very_good, HomotopicalAlgebra.LeftHomotopyRel.equivalence, HomotopicalAlgebra.RightHomotopyRel.equivalence, HomotopicalAlgebra.LeftHomotopyClass, HomotopicalAlgebra.FibrantBrownFactorization, HomotopicalAlgebra.leftHomotopyClassToHom, HomotopicalAlgebra.BifibrantObject, HomotopicalAlgebra.CofibrantObject, HomotopicalAlgebra.BifibrantObject.toHoCat, HomotopicalAlgebra.CofibrantObject.HoCat]
  E1: auto
families: []
requires: [V24.C04, V24.C05, V25.C03, V25.C04, V27.C01, V27.C03, V27.C04, V27.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Model categories

### Overview

A model category is a category with three classes of maps: weak equivalences, fibrations and cofibrations. The axioms make it possible to compute the localization at the weak equivalences with homotopies. This section states the axioms, defines cofibrant and fibrant objects, cylinders, path objects and the two homotopy relations. It proves the retract argument, the lemma of K. S. Brown, the agreement of the two relations and the Whitehead theorem, and it then gives the fundamental lemma on the homotopy category.

All declarations of this section are in the namespace `HomotopicalAlgebra`. The notation in the text uses $g \circ f$ for "first $f$, then $g$". Lean writes `f ≫ g` for the same map.

### Definitions

The lifting language of Volume 25, Chapter 3 is the base. A map $i : A \to B$ has the *left lifting property* against $p : X \to Y$ when each commutative square $p \circ u = v \circ i$ has a diagonal $d : B \to X$ with $d \circ i = u$ and $p \circ d = v$. In this case $p$ has the right lifting property against $i$.

**Definition (Category with weak equivalences, fibrations and cofibrations).** A category with weak equivalences is a category $\mathcal{C}$ with a class of maps $\mathrm{W}$. The classes $\mathrm{Fib}$ of fibrations and $\mathrm{Cof}$ of cofibrations are given in the same way. The *trivial fibrations* are $\mathrm{Fib} \cap \mathrm{W}$ and the *trivial cofibrations* are $\mathrm{Cof} \cap \mathrm{W}$.

In Mathlib the three structures are three separate classes, `CategoryWithWeakEquivalences`, `CategoryWithFibrations` and `CategoryWithCofibrations`. The statements `WeakEquivalence f`, `Fibration f` and `Cofibration f` are type classes.

**Definition (Model category).** A model category is a category $\mathcal{C}$ with weak equivalences, fibrations and cofibrations, with these axioms:

1. (CM1) $\mathcal{C}$ has finite limits and finite colimits.
2. (CM2) $\mathrm{W}$ has the two out of three property: if two of $f$, $g$ and $g \circ f$ are in $\mathrm{W}$, then the third is in $\mathrm{W}$.
3. (CM3) $\mathrm{W}$, $\mathrm{Fib}$ and $\mathrm{Cof}$ are stable under retracts.
4. (CM4) Each trivial cofibration has the left lifting property against each fibration, and each cofibration has the left lifting property against each trivial fibration.
5. (CM5) Each map factors as a trivial cofibration followed by a fibration, and as a cofibration followed by a trivial fibration.

The class `ModelCategory` has the fields `cm1a`, `cm1b`, `cm2`, `cm3a`, `cm3b`, `cm3c`, `cm4a`, `cm4b`, `cm5a` and `cm5b`. This is the closed model category of Quillen, with factorizations that are not functorial.

**Definition (Cofibrant and fibrant objects).** An object $X$ is *cofibrant* if the map $\varnothing \to X$ from an initial object is a cofibration. It is *fibrant* if $X \to *$ to a terminal object is a fibration. It is *bifibrant* if it is both.

The predicates are `IsCofibrant X` and `IsFibrant X`. The full subcategories are `CofibrantObject C`, `FibrantObject C` and `BifibrantObject C`.

**Definition (Cylinder object).** A *cylinder* for $X$ is an object $I$ with maps $i_0, i_1 : X \to I$ and a weak equivalence $\pi : I \to X$ such that $\pi \circ i_0 = \pi \circ i_1 = \mathrm{id}_X$. Let $i = (i_0, i_1) : X \sqcup X \to I$. The cylinder is *good* if $i$ is a cofibration. It is *very good* if it is good and $\pi$ is a fibration.

**Definition (Path object).** A *path object* for $Y$ is the dual: an object $P$ with $p_0, p_1 : P \to Y$ and a weak equivalence $\iota : Y \to P$ with $p_0 \circ \iota = p_1 \circ \iota = \mathrm{id}_Y$. It is *good* if $(p_0, p_1) : P \to Y \times Y$ is a fibration, and *very good* if also $\iota$ is a cofibration. The structure is `PathObject`.

CM5 applied to the codiagonal $X \sqcup X \to X$ gives a very good cylinder: factor it as a cofibration $i$ followed by a trivial fibration $\pi$. This is `Cylinder.exists_very_good`. The dual factorization of the diagonal $Y \to Y \times Y$ gives a very good path object.

**Definition (Left and right homotopy).** Let $f, g : X \to Y$. A *left homotopy* from $f$ to $g$ is a cylinder $I$ for $X$ and a map $h : I \to Y$ with $h \circ i_0 = f$ and $h \circ i_1 = g$. A *right homotopy* from $f$ to $g$ is a path object $P$ for $Y$ and a map $k : X \to P$ with $p_0 \circ k = f$ and $p_1 \circ k = g$. The relations $f \sim_l g$ and $f \sim_r g$ say that such homotopies exist.

In Mathlib, `LeftHomotopyRel f g` says that there is a cylinder `P` and a term of `P.LeftHomotopy f g`.

### Theorems and proofs

**Lemma (Retract argument).** In a model category, a map is a cofibration if and only if it has the left lifting property against each trivial fibration. Dually, a map is a fibration if and only if it has the right lifting property against each trivial cofibration.

*Proof.* A cofibration has the property by CM4. Let $f : A \to B$ have the left lifting property against each trivial fibration. By CM5, $f = p \circ j$ with $j : A \to Z$ a cofibration and $p : Z \to B$ a trivial fibration. The square $p \circ j = \mathrm{id}_B \circ f$ has a diagonal $r : B \to Z$ has $r \circ f = j$ and $p \circ r = \mathrm{id}_B$. Thus the diagram $A = A = A$ above $B \xrightarrow{r} Z \xrightarrow{p} B$ shows that $f$ is a retract of $j$. By CM3, $f$ is a cofibration. The other statements follow by the same argument with CM5 and duality. $\square$

The same argument gives the other three lifting characterizations: `cofibrations_rlp`, `fibrations_llp`, `trivialCofibrations_rlp` and `trivialFibrations_llp`. Thus cofibrations and trivial cofibrations are stable under composition and cobase change, and dually for fibrations.

**Corollary.** Let $X$ be cofibrant and let $I$ be a good cylinder for $X$. Then $i_0$ and $i_1$ are trivial cofibrations, and $I$ is cofibrant.

*Proof.* The inclusion $X \to X \sqcup X$ of the first summand is the cobase change of $\varnothing \to X$ along $\varnothing \to X$, so it is a cofibration. The map $i_0$ is the composite of this inclusion and the cofibration $i$, so it is a cofibration. By CM2 and $\pi \circ i_0 = \mathrm{id}_X$, it is a weak equivalence. The map $\varnothing \to I$ is the composite of $\varnothing \to X$ and $i_0$, so $I$ is cofibrant. The case of $i_1$ is the same. $\square$

**Lemma (Brown factorization).** Let $f : X \to Y$ be a map between cofibrant objects. Then $f = p \circ j$, where $j$ is a cofibration, $p$ is a trivial fibration, and $p$ has a section $s$ that is a trivial cofibration. If $f$ is a weak equivalence, then $j$ is a trivial cofibration.

*Proof.* By CM5, $(f, \mathrm{id}_Y) : X \sqcup Y \to Y$ is $p \circ c$ with $c : X \sqcup Y \to Z$ a cofibration and $p$ a trivial fibration. Let $j$ and $s$ be the components of $c$. Then $p \circ j = f$ and $p \circ s = \mathrm{id}_Y$. The inclusion $X \to X \sqcup Y$ is a cobase change of $\varnothing \to Y$, so it is a cofibration, and $j$ is a cofibration. In the same way $s$ is a cofibration. By CM2, $s$ is a weak equivalence, and $j$ is one if $f$ is. $\square$ This is `CofibrantBrownFactorization`.

The dual, `FibrantBrownFactorization`, factors a map between fibrant objects as $q \circ j$, with $q$ a fibration and $j$ a trivial cofibration that has a trivial fibration $r$ as a retraction.

**Theorem (Left homotopy is an equivalence relation).** Let $X$ be cofibrant. Then left homotopy is an equivalence relation on the maps $X \to Y$.

*Proof.* Reflexivity: for a cylinder $I$, the map $f \circ \pi$ is a left homotopy from $f$ to $f$. Symmetry: exchange $i_0$ and $i_1$ in the cylinder. This is `Cylinder.symm`.

For transitivity, first make the cylinders good. Factor $i : X \sqcup X \to I$ as a cofibration $c : X \sqcup X \to I'$ followed by a trivial fibration $q$. Then $I'$, with the components of $c$ and with $\pi \circ q$, is a good cylinder by CM2, and $h \circ q$ is a left homotopy from $f$ to $g$.

Now let $h : I \to Y$ go from $f$ to $g$ and $h' : I' \to Y$ from $g$ to $k$, with good cylinders. Let $J$ be the pushout of $I \xleftarrow{i_1} X \xrightarrow{i'_0} I'$, with $a : I \to J$ and $b : I' \to J$. By the corollary, $i'_0$ is a trivial cofibration, so its cobase change $a$ is one. The maps $\pi$ and $\pi'$ give $\pi_J : J \to X$ with $\pi_J \circ a = \pi$, a weak equivalence by CM2. So $J$ with $a \circ i_0$, $b \circ i'_1$ and $\pi_J$ is a cylinder. Since $h \circ i_1 = g = h' \circ i'_0$, the maps $h$ and $h'$ give $h_J : J \to Y$, a left homotopy from $f$ to $k$. This is `Cylinder.trans`. $\square$

Dually, right homotopy is an equivalence relation when $Y$ is fibrant. Let $\pi^l(X, Y)$ be the set `LeftHomotopyClass X Y`. If $h$ is a left homotopy from $f$ to $g$, then $u \circ h$ is one from $u \circ f$ to $u \circ g$.

**Theorem (Left and right homotopy agree).** Let $X$ be cofibrant, $Y$ fibrant and $f, g : X \to Y$. Then $f \sim_l g$ if and only if $f \sim_r g$.

*Proof.* Let $h : I \to Y$ be a left homotopy from $f$ to $g$. By the proof above, $I$ can be taken good. Let $P$ be a good path object for $Y$. The square

$$\begin{array}{ccc} X & \xrightarrow{\iota \circ f} & P \\ {\scriptstyle i_0}\downarrow & & \downarrow{\scriptstyle (p_0, p_1)} \\ I & \xrightarrow{(f \circ \pi,\ h)} & Y \times Y \end{array}$$

commutes: both composites are $(f, f)$. The left map is a trivial cofibration by the corollary, and the right map is a fibration. So CM4 gives a diagonal $K : I \to P$. Let $k = K \circ i_1$. Then $p_0 \circ k = f \circ \pi \circ i_1 = f$ and $p_1 \circ k = h \circ i_1 = g$. So $k$ is a right homotopy from $f$ to $g$. The converse is the dual argument, which uses that $Y$ is fibrant. $\square$

So for $X$ cofibrant and $Y$ fibrant there is one relation $\sim$ on the maps $X \to Y$, and it is compatible with composition on both sides.

**Lemma.** Let $X$ be cofibrant and let $p : Y \to Z$ be a trivial fibration. Then $p_* : \pi^l(X, Y) \to \pi^l(X, Z)$ is bijective.

*Proof.* Surjectivity: for $v : X \to Z$, the square with left side $\varnothing \to X$ and right side $p$ has a diagonal $u : X \to Y$ by CM4, and $p \circ u = v$. Injectivity: let $h : I \to Z$ be a left homotopy from $p \circ u$ to $p \circ u'$, with $I$ good. The square with top $(u, u') : X \sqcup X \to Y$, left side the cofibration $i$, right side $p$ and bottom $h$ commutes. A diagonal $H : I \to Y$ is a left homotopy from $u$ to $u'$. $\square$

**Theorem (Postcomposition with a weak equivalence).** Let $X$ be cofibrant, and let $g : Y \to Z$ be a weak equivalence between fibrant objects. Then $g_* : \pi^l(X, Y) \to \pi^l(X, Z)$ is bijective.

*Proof.* By the dual Brown factorization, $g = q \circ j$ where $j : Y \to W$ is a trivial cofibration with a retraction $r$ that is a trivial fibration, and $q$ is a fibration. By CM2, $q$ is a weak equivalence, so it is a trivial fibration. By the lemma, $q_*$ and $r_*$ are bijective. Since $r_* \circ j_* = \mathrm{id}$, the map $j_* = (r_*)^{-1}$ is bijective. Thus $g_* = q_* \circ j_*$ is bijective. $\square$ This is `LeftHomotopyClass.postcomp_bijective_of_weakEquivalence`.

**Theorem (Whitehead).** Let $f : X \to Y$ be a weak equivalence between bifibrant objects. Then there is $g : Y \to X$ with $g \circ f \sim \mathrm{id}_X$ and $f \circ g \sim \mathrm{id}_Y$.

*Proof.* The object $Y$ is cofibrant and $f$ is a weak equivalence between fibrant objects. By the theorem above, $f_* : \pi^l(Y, X) \to \pi^l(Y, Y)$ is surjective, so there is $g$ with $f \circ g \sim \mathrm{id}_Y$. Then $f \circ (g \circ f) = (f \circ g) \circ f \sim f = f \circ \mathrm{id}_X$, because $\sim$ is compatible with composition on the right for the cofibrant source $X$ and the fibrant target $Y$. The map $f_* : \pi^l(X, X) \to \pi^l(X, Y)$ is injective, so $g \circ f \sim \mathrm{id}_X$. $\square$ Mathlib states it as `RightHomotopyClass.whitehead`.

**Theorem (Fundamental lemma).** Let $L : \mathcal{C} \to \mathcal{H}$ be a localization of $\mathcal{C}$ at the weak equivalences. Let $X$ be cofibrant and $Y$ fibrant. Then $f \mapsto L(f)$ induces a bijection $\pi^l(X, Y) \to \mathrm{Hom}_{\mathcal{H}}(LX, LY)$.

*Proof.* The proof in Mathlib has three steps, given here in outline. First, the bifibrant objects modulo $\sim$ form a category $\mathrm{Ho}_{cf}$. A functor that inverts weak equivalences identifies $i_0$ and $i_1$ for a very good cylinder, because both are sections of the weak equivalence $\pi$. So it identifies homotopic maps, and $\mathrm{Ho}_{cf}$ is the localization of the bifibrant objects. Second, CM5 gives each object a bifibrant resolution, so the bifibrant objects have the same localization as $\mathcal{C}$. Third, the theorem on postcomposition and its dual compare $\pi^l(X, Y)$ with the classes between the resolutions. $\square$

In Mathlib the first step is the instance that `BifibrantObject.toHoCat` is a localization, where `BifibrantObject.HoCat` is the quotient category. The third step is `bijective_leftHomotopyClassToHom`.

### Examples

**Example (Trivial model structure).** Let $\mathcal{C}$ have finite limits and finite colimits. Let $\mathrm{W}$ be the isomorphisms and let $\mathrm{Fib} = \mathrm{Cof}$ be all maps. CM2 and CM3 are clear. A trivial cofibration is an isomorphism, and an isomorphism lifts against each map, so CM4 holds. The factorizations $f = f \circ \mathrm{id}$ and $f = \mathrm{id} \circ f$ give CM5. Here $f \sim g$ means $f = g$, and the homotopy category is $\mathcal{C}$.

**Example (Bounded below cochain complexes).** Let $\mathcal{A}$ be an abelian category with enough injectives. In `CochainComplex.Plus` of $\mathcal{A}$ take the monomorphisms as cofibrations, the quasi-isomorphisms as weak equivalences, and the degreewise epimorphisms with an injective kernel in each degree as fibrations. This is the injective model structure of Quillen. Each object is cofibrant, and the fibrant objects are the bounded below complexes of injectives. By the fundamental lemma, maps in $D^+(\mathcal{A})$ to a complex of injectives are homotopy classes of chain maps.

::: mathlib
`CochainComplex.Plus.modelCategoryQuillen.cofibration_iff` · `Mathlib.Algebra.Homology.ModelCategory.Injective`

The instance on `CochainComplex.Plus C` is scoped in `CochainComplex.Plus.modelCategoryQuillen`. This lemma says that the cofibrations are the monomorphisms.

<?decl CochainComplex.Plus.modelCategoryQuillen.cofibration_iff?>
:::

**Example (Opposite and over categories).** If $\mathcal{C}$ is a model category, then $\mathcal{C}^{\mathrm{op}}$ is one, with the same weak equivalences and with fibrations and cofibrations exchanged. For an object $S$, the category $\mathcal{C}/S$ is a model category, where a map is a weak equivalence, fibration or cofibration if its image in $\mathcal{C}$ is one. This is the instance `ModelCategory.over`.

In Lean the agreement theorem reads as follows.

```lean
open CategoryTheory HomotopicalAlgebra in
example {C : Type*} [Category C] [ModelCategory C] {X Y : C}
    [IsCofibrant X] [IsFibrant Y] (f g : X ⟶ Y) :
    LeftHomotopyRel f g ↔ RightHomotopyRel f g :=
  leftHomotopyRel_iff_rightHomotopyRel
```

### The library around it

The instances in `Instances` show that `(cofibrations C, trivialFibrations C)` and `(trivialCofibrations C, fibrations C)` are weak factorization systems. The constructor `ModelCategory.mk'` builds a model category from these two systems.

::: mathlib
`HomotopicalAlgebra.ModelCategory.hasLiftingProperty_of_joyalTrick` · `Mathlib.AlgebraicTopology.ModelCategory.JoyalTrick`

The trick of Joyal: if CM1, CM2, CM3, CM5 and the first half of CM4 hold, and the cofibrations are stable under composition and cobase change, then the second half of CM4 holds. The source cites Jardine, *Simplicial presheaves*.

<?decl HomotopicalAlgebra.ModelCategory.hasLiftingProperty_of_joyalTrick?>
:::

The categories `CofibrantObject.HoCat` and `FibrantObject.HoCat` are quotients by right and left homotopy. The files `DerivabilityStructureCofibrant` and `DerivabilityStructureFibrant` give derivability structures in the sense of Kahn and Maltsiniotis. The inclusion of the cofibrant objects, `HomotopicalAlgebra.CofibrantObject.localizerMorphism C`, is a left derivability structure, by the instance `HomotopicalAlgebra.CofibrantObject.instIsLeftDerivabilityStructureWeakEquivalencesLocalizerMorphism`: each object has a cofibrant resolution, and the category of these resolutions is connected. Dually, the inclusion of the fibrant objects, `HomotopicalAlgebra.FibrantObject.localizerMorphism C`, is a right derivability structure.

Mathlib in this edition has no instance of `ModelCategory` on simplicial sets or on topological spaces. The file `AlgebraicTopology.SimplicialSet.CategoryWithFibrations` puts the Kan fibrations and the monomorphisms on `SSet` in a scoped namespace, but the model axioms are not proved there.

Common errors of a learner: The first error is to read `f ≫ g` as "$f$ after $g$". The second error is to use `LeftHomotopyRel.equivalence` without `[IsCofibrant X]`. The third error is to search for a model structure on `SSet` by instance search; there is none. The fourth error is to forget that the instance on `CochainComplex.Plus C` is scoped.

### Exercises

1. (A) Show that each isomorphism of a model category is a weak equivalence. *Hint:* factor $\mathrm{id}_X = p \circ j$ by CM5 with $j$ a trivial cofibration, show that $\mathrm{id}_X$ is a retract of $j$, and then show that an isomorphism $f : A \to B$ is a retract of $\mathrm{id}_B$.
2. (A) Show that the trivial fibrations are stable under base change. *Hint:* use the retract argument.
3. (A) In the trivial model structure, describe the cylinders of an object $X$ and show that $f \sim_l g$ implies $f = g$. *Hint:* $\pi$ is an isomorphism.
4. (B) Let $X$ be cofibrant, $Y$ fibrant and $f \sim g : X \to Y$. Let $u : W \to X$ be a map from a cofibrant object $W$. Show that $f \circ u \sim g \circ u$. *Hint:* use a right homotopy $k : X \to P$ and the map $k \circ u$.
5. (B) Prove the dual of the lemma on trivial fibrations: let $Y$ be fibrant and $j : W \to X$ a trivial cofibration. Show that $j^* : \pi^r(X, Y) \to \pi^r(W, Y)$ is bijective.
6. (C) Let $\mathcal{A}$ have enough injectives and let $M, N \in \mathcal{A}$, in degree $0$. Use the injective model structure and the fundamental lemma to show that $\mathrm{Hom}_{D^+(\mathcal{A})}(M, N[n]) \cong \mathrm{Ext}^n(M, N)$. *Hint:* an injective resolution $N \to J$ is a trivial cofibration to a fibrant object.

### Notes and history

Quillen defined model categories in 1967 in *Homotopical Algebra*, with cylinders, path objects and the homotopy category. The factorization lemma is from the 1973 paper of K. S. Brown, cited in the source file `BrownLemma`.

The Mathlib Authors of all files in `AlgebraicTopology.ModelCategory`: Joël Riou.

### Reference

<?reference?>
