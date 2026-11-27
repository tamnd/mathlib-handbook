---
title: Exact functors, projectives and Grothendieck categories
kind: theory
modules:
  - Mathlib.CategoryTheory.Abelian.Exact
  - Mathlib.CategoryTheory.Preadditive.LeftExact
  - Mathlib.CategoryTheory.Preadditive.Projective.Basic
  - Mathlib.CategoryTheory.Preadditive.Injective.Basic
  - Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
  - Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
  - Mathlib.CategoryTheory.Abelian.FreydMitchell
explains:
  E3: [CategoryTheory.Functor.preservesFiniteLimits_of_preservesKernels, CategoryTheory.Projective, CategoryTheory.EnoughProjectives, CategoryTheory.Injective, CategoryTheory.Injective.injective_iff_projective_op, CategoryTheory.AB4, CategoryTheory.AB5, CategoryTheory.AB4.of_AB5, CategoryTheory.IsGrothendieckAbelian, CategoryTheory.Abelian.freyd_mitchell]
  E2: [CategoryTheory.ShortComplex.exact_iff_image_eq_kernel, CategoryTheory.Functor.preservesHomology_of_preservesMonos_and_cokernels, CategoryTheory.Functor.reflects_exact_of_faithful, CategoryTheory.Functor.preservesFiniteColimits_of_preservesCokernels, CategoryTheory.Projective.factorThru, CategoryTheory.Projective.projective_iff_preservesEpimorphisms_coyoneda_obj, CategoryTheory.ProjectivePresentation, CategoryTheory.Projective.instBiproduct, CategoryTheory.Retract.projective, CategoryTheory.Adjunction.map_projective, CategoryTheory.Injective.factorThru, CategoryTheory.EnoughInjectives, CategoryTheory.Injective.injective_of_adjoint, CategoryTheory.AB4Star, CategoryTheory.AB5Star, CategoryTheory.IsGrothendieckAbelian.hasLimits, CategoryTheory.IsGrothendieckAbelian.ab4OfSize, CategoryTheory.Abelian.FreydMitchell.EmbeddingRing, CategoryTheory.Abelian.FreydMitchell.functor]
  E1: auto
families: []
requires: [V07, V24.C03, V24.C04, V24.C05, V24.C08, V25.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Exact functors, projectives and Grothendieck categories

### Overview

The last section of this chapter is about functors and about objects with special lifting properties. An additive functor between abelian categories need not keep exact sequences exact. It is *left exact* if it preserves kernels, *right exact* if it preserves cokernels, and *exact* if it does both. The functor $\mathrm{Hom}(P, -)$ is always left exact, and it is exact exactly when $P$ is projective. Projective and injective objects are the raw material of derived functors in Volume 26. The section then states the axioms AB3 to AB5 of Grothendieck on colimits, defines Grothendieck abelian categories, and ends with the Freyd-Mitchell embedding theorem, which Mathlib proves in full: each abelian category embeds into a category of modules by a full, faithful and exact functor.

In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`. The categories $C$ and $D$ are abelian, and functors are additive.

### Definitions

**Definition (Exact functors).** A functor $F : C \to D$ is *left exact* if it preserves finite limits, *right exact* if it preserves finite colimits, and *exact* if it is both.

By the theorem below, an additive functor is left exact if and only if it preserves kernels. Then $0 \to A \to B \to C$ exact implies $0 \to FA \to FB \to FC$ exact, since such a sequence says that $A \to B$ is a kernel of $B \to C$.

**Definition (Projective and injective objects).** An object $P$ is *projective* if for each epimorphism $e : E \to X$ and each $f : P \to X$ there is $f' : P \to E$ with $e \circ f' = f$. An object $I$ is *injective* if for each monomorphism $m : X \to E$ and each $f : X \to I$ there is $f' : E \to I$ with $f' \circ m = f$. The category has *enough projectives* if each object is the target of an epimorphism from a projective object, and *enough injectives* if each object is the source of a monomorphism into an injective object.

The lift $f'$ is not unique. Mathlib chooses one, `Projective.factorThru f e`. An epimorphism $P \to X$ from a projective is a `ProjectivePresentation` of $X$.

**Definition (Grothendieck axioms).** Let $C$ be abelian.

- *AB3*: $C$ has all small coproducts, so all small colimits.
- *AB4*: AB3 holds, and a coproduct of short exact sequences is short exact.
- *AB5*: AB3 holds, and a filtered colimit of short exact sequences is short exact.

The dual axioms AB3* to AB5* are AB3 to AB5 for $C^{\mathrm{op}}$: products, and cofiltered limits.

**Definition (Grothendieck abelian category).** An abelian category is *Grothendieck* if it satisfies AB5, has small hom sets, and has a *separator*: an object $G$ such that for $f \neq g : X \to Y$ there is $h : G \to X$ with $f \circ h \neq g \circ h$.

::: mathlib

`CategoryTheory.IsGrothendieckAbelian` · `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`

A class with the fields `locallySmall`, `hasFilteredColimitsOfSize`, `ab5OfSize` and `hasSeparator`, for a universe `w`. The file derives the instances `IsGrothendieckAbelian.hasColimits`, `IsGrothendieckAbelian.hasLimits` and `IsGrothendieckAbelian.ab4OfSize`. The class `AB5 C` says `HasExactColimitsOfShape J C` for each filtered `J`.

<?decl CategoryTheory.IsGrothendieckAbelian?>
:::

### Theorems and proofs

**Theorem (Kernels suffice).** An additive functor $F : C \to D$ that preserves kernels preserves all finite limits. Dually, an additive functor that preserves cokernels preserves all finite colimits.

*Proof.* Finite limits are built from a terminal object, binary products and equalizers, by Volume 24, Chapter 4. A zero object goes to a zero object, because $1_0 = 0$ gives $1_{F0} = F(0) = 0$. Binary products are biproducts, and $F$ preserves biproducts by Chapter 1, Section 1. The equalizer of $a, b : X \to Y$ is the kernel of $a - b$, and $F(a - b) = Fa - Fb$, so $F$ sends it to the kernel of $Fa - Fb$, which is the equalizer of $Fa$ and $Fb$. $\square$

Mathlib proves the theorem under the weaker hypothesis that $F$ preserves zero morphisms, with a direct construction of the binary products from kernels.

**Theorem (Hom functors and projectives).** For each object $P$, the functor $\mathrm{Hom}(P, -) : C \to \mathrm{Ab}$ is left exact. It is exact if and only if $P$ is projective.

*Proof.* A kernel $k : K \to B$ of $g : B \to C$ has the universal property that maps $T \to K$ correspond to maps $T \to B$ killed by $g$. For $T = P$ this says that $\mathrm{Hom}(P, K)$ is the kernel of $g_* : \mathrm{Hom}(P, B) \to \mathrm{Hom}(P, C)$. So $\mathrm{Hom}(P, -)$ preserves kernels, and the previous theorem gives left exactness. A left exact functor $G$ that sends epimorphisms to epimorphisms is exact. To see this, let $c : Y \to Q$ be the cokernel of $f : X \to Y$, and factor $f = i \circ e$ with $e$ epi and $i$ mono. Then $c$ is the cokernel of $i$ and $i$ is the kernel of $c$. So $Gi$ is the kernel of $Gc$, and $Gc$ is epi, hence the cokernel of its kernel $Gi$. As $Ge$ is epi, the cokernel of $Gf = Gi \circ Ge$ is the cokernel of $Gi$, which is $Gc$. Conversely, an exact functor preserves epimorphisms, as the cokernel of an epimorphism is zero. In $\mathrm{Ab}$ an epimorphism is a surjection. The condition that $e_* : \mathrm{Hom}(P, E) \to \mathrm{Hom}(P, X)$ is surjective for each epimorphism $e$ is the definition of a projective object. $\square$

**Proposition (Closure properties).** A finite biproduct of projectives is projective, and a retract of a projective is projective. If $L \dashv R$ is an adjunction and $R$ preserves epimorphisms, then $L$ sends projectives to projectives.

*Proof.* For $P_1 \oplus P_2$ and $f : P_1 \oplus P_2 \to X$, lift $f \iota_1$ and $f \iota_2$ through $e$ to $g_1$ and $g_2$, and take $[g_1, g_2]$. For a retract $Q \xrightarrow{s} P \xrightarrow{r} Q$ with $r s = 1$ and $f : Q \to X$, lift $f r$ to $g : P \to E$, and take $g s$: then $e g s = f r s = f$. For the adjunction, a map $LP \to X$ corresponds to a map $P \to RX$. If $e : E \to X$ is epi, then $Re$ is epi, so the map lifts through $Re$, and the adjoint of the lift is a lift through $e$, by naturality of the adjunction bijection. $\square$

**Theorem (Splitting).** Let $0 \to A \xrightarrow{f} B \xrightarrow{g} P \to 0$ be short exact with $P$ projective. Then $B \cong A \oplus P$, compatibly with $f$ and $g$.

*Proof.* Lift $1_P$ through the epimorphism $g$ to $s : P \to B$ with $g s = 1_P$. The map $1_B - s g$ satisfies $g (1 - s g) = g - g = 0$, so it factors through the kernel $f$: there is $r : B \to A$ with $f r = 1 - s g$. Then $f r f = f - s g f = f$, and $f$ is mono, so $r f = 1_A$. Also $f r s = s - s g s = 0$, so $r s = 0$. With $g f = 0$ and $g s = 1$, the maps $(f, s)$ and $(r, g)$ form a bicone on $(A, P)$ with $f r + s g = 1_B$. By the total identity of Chapter 1, Section 1, $B$ is the biproduct. $\square$

**Theorem (Duality and AB5).** An object $I$ of $C$ is injective if and only if it is projective in $C^{\mathrm{op}}$. If $C$ satisfies AB5, it satisfies AB4.

*Proof.* The first claim is the definition read in $C^{\mathrm{op}}$, where monomorphisms become epimorphisms. For the second, let $(X_j)_{j \in J}$ be a family. Its coproduct is the filtered colimit, over the finite subsets $S \subseteq J$, of the finite coproducts $\bigoplus_{j \in S} X_j$. A finite direct sum of short exact sequences is short exact, since finite coproducts are biproducts and the biproduct of two kernels is the kernel of the biproduct map. By AB5, the filtered colimit of these short exact sequences is short exact. $\square$

**Theorem (Freyd-Mitchell embedding, stated).** For each abelian category $C$ there are a ring $R$ and a functor $F : C \to \mathrm{ModuleCat}\, R$ that is full, faithful, and preserves finite limits and finite colimits.

The proof in Mathlib takes the route of Kashiwara and Schapira. It shows that a Grothendieck abelian category has all limits and enough injectives, the second by the small object argument of Chapter 3. It then embeds $C$ into the opposite of a Grothendieck category, the ind-objects of $C^{\mathrm{op}}$, and uses $\mathrm{Hom}(G, -)$ for a projective separator $G$ of that opposite category.

The theorem justifies the diagram chases of Section 2 in a strong form: a statement about finite diagrams, exactness and commutativity that holds for modules holds in every abelian category. The method of refinements gives the same results without the embedding.

### Examples

**Example (Modules).** In `ModuleCat R`, a module is projective in the categorical sense if and only if it is a projective module in the sense of Volume 7, a direct summand of a free module. Free modules are projective, and the free module on the underlying set of $M$ maps onto $M$, so there are enough projectives. The category satisfies AB5, because a filtered colimit of modules is a quotient of a direct sum, computed on underlying sets, and filtered colimits of sets commute with finite limits. The ring $R$ is a separator: $f \neq g : X \to Y$ differ at some $x \in X$, and $h(r) = r x$ separates them. So `ModuleCat R` is Grothendieck.

**Example (Injective abelian groups).** In $\mathrm{Ab}$, the group $\mathbb{Q}/\mathbb{Z}$ is injective, by Baer's criterion and divisibility, Volume 7. Each abelian group embeds into a product of copies of $\mathbb{Q}/\mathbb{Z}$, so $\mathrm{Ab}$ has enough injectives. Mathlib has the instances `AddCommGrpCat.enoughInjectives` and `ModuleCat.enoughInjectives`.

**Counterexample (AB5* fails for abelian groups).** Let $p$ be a prime and consider the short exact sequences $0 \to p^n \mathbb{Z} \to \mathbb{Z} \to \mathbb{Z}/p^n \to 0$, with the inclusions and projections as $n$ grows. The limit of the left terms is $\bigcap_n p^n \mathbb{Z} = 0$, the limit of the middle terms is $\mathbb{Z}$, and the limit of the right terms is the $p$-adic integers $\mathbb{Z}_p$. The limit sequence $0 \to 0 \to \mathbb{Z} \to \mathbb{Z}_p \to 0$ is not exact, since $\mathbb{Z}$ is countable and $\mathbb{Z}_p$ is not. So cofiltered limits in $\mathrm{Ab}$ are not exact, and $\mathrm{Ab}^{\mathrm{op}}$ does not satisfy AB5.

### The library around it

::: mathlib

`CategoryTheory.Projective` · `Mathlib.CategoryTheory.Preadditive.Projective.Basic`

A class with one field, `factors`. The criterion `Projective.projective_iff_preservesEpimorphisms_coyoneda_obj` is the theorem on Hom functors in a general category. Instances give projectivity of biproducts and coproducts, and `Retract.projective` and `Adjunction.map_projective` are the closure properties. The class `EnoughProjectives` asks for a `ProjectivePresentation` of each object.

<?decl CategoryTheory.Projective?>
:::

::: mathlib

`CategoryTheory.Abelian.freyd_mitchell` · `Mathlib.CategoryTheory.Abelian.FreydMitchell`

The statement: for `C : Type u` with `Category.{v} C` and `Abelian C`, there exist a ring `R : Type (max u v)` and `F : C ⥤ ModuleCat R` with `F.Full`, `F.Faithful`, `PreservesFiniteLimits F` and `PreservesFiniteColimits F`. The ring is `FreydMitchell.EmbeddingRing C` and the functor is `FreydMitchell.functor C`.

<?decl CategoryTheory.Abelian.freyd_mitchell?>
:::

The theorem `IsGrothendieckAbelian.enoughInjectives`, in the file `Abelian.GrothendieckCategory.EnoughInjectives`, gives enough injectives in each Grothendieck abelian category. In `Abelian.Exact`, the theorem `ShortComplex.exact_iff_image_eq_kernel` compares the exactness of Mathlib with the form $\mathrm{im}\, f = \ker g$.

Common errors of a learner:

- `Projective P` is a `Prop`, but the lift `Projective.factorThru` is a chosen function. Two calls with the same arguments give the same lift, but no other property than `factorThru_comp` holds.
- In Mathlib a left exact functor is a functor with `PreservesFiniteLimits`. Exactness of sequences is `ShortComplex.Exact`, and the link is `Functor.preservesHomology_of_preservesMonos_and_cokernels` and its variants.

### Exercises

1. (A) Show that a zero object is projective and injective.
2. (A) Show that $\mathrm{Hom}(-, I) : C^{\mathrm{op}} \to \mathrm{Ab}$ is exact if and only if $I$ is injective.
3. (B) Show that in `ModuleCat ℤ` the module $\mathbb{Z}/2$ is neither projective nor injective. *Hint:* use the epimorphism $\mathbb{Z} \to \mathbb{Z}/2$ and the monomorphism $\mathbb{Z}/2 \to \mathbb{Z}/4$.
4. (B) Let $F \dashv G$ be an adjunction of additive functors between abelian categories. Prove that $G$ is left exact and $F$ is right exact.
5. (B) Prove that the functor $- \otimes \mathbb{Z}/2$ on abelian groups is right exact but not left exact. *Hint:* apply it to $0 \to \mathbb{Z} \xrightarrow{2} \mathbb{Z}$.
6. (C) Prove that a Grothendieck abelian category with a projective separator $G$ is equivalent to a category of modules, if $G$ is also compact: $\mathrm{Hom}(G, -)$ preserves coproducts. *Hint:* use $\mathrm{Hom}(G, -)$ and the ring $\mathrm{End}(G)^{\mathrm{op}}$.

### Notes and history

The axioms AB3 to AB5 and their duals are from Grothendieck's paper on homological algebra of 1957, which also proves that a category with AB5 and a generator has enough injectives. Exact functors and derived functors go back to the book of Cartan and Eilenberg of 1956. The embedding theorem is due to Freyd and to Mitchell, in the early 1960s. The Mathlib proof follows Kashiwara and Schapira, *Categories and Sheaves*.

The Mathlib files are by Markus Himmel, Adam Topaz, Johan Commelin and Jakob von Raumer (exactness), Markus Himmel and Jakob von Raumer (left exact functors), Markus Himmel and Kim Morrison (projectives), Jujian Zhang and Kevin Buzzard (injectives), Dagur Asgeirsson, Isaac Hernando, Coleton Kotch and Adam Topaz (the Grothendieck axioms), Paul Reichert (Grothendieck categories) and Markus Himmel (the embedding theorem).

### Reference

<?reference?>
