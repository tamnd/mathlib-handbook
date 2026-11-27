---
title: Pseudoelements and the diagram lemmas
kind: theory
modules:
  - Mathlib.CategoryTheory.Abelian.Pseudoelements
  - Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
  - Mathlib.CategoryTheory.Abelian.Refinements
explains:
  E3: [CategoryTheory.epi_iff_surjective_up_to_refinements, CategoryTheory.ShortComplex.exact_iff_exact_up_to_refinements, CategoryTheory.Abelian.mono_of_epi_of_mono_of_mono, CategoryTheory.Abelian.epi_of_epi_of_epi_of_mono, CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono, CategoryTheory.Abelian.Pseudoelement]
  E2: [CategoryTheory.surjective_up_to_refinements_of_epi, CategoryTheory.ShortComplex.Exact.exact_up_to_refinements, CategoryTheory.Abelian.mono_of_epi_of_mono_of_mono', CategoryTheory.Abelian.PseudoEqual, CategoryTheory.Abelian.Pseudoelement.pseudoApply, CategoryTheory.Abelian.Pseudoelement.pseudoZero, CategoryTheory.Abelian.Pseudoelement.epi_of_pseudo_surjective, CategoryTheory.Abelian.Pseudoelement.pseudo_surjective_of_epi, CategoryTheory.Abelian.Pseudoelement.pseudo_injective_of_mono, CategoryTheory.Abelian.Pseudoelement.exact_of_pseudo_exact, CategoryTheory.Abelian.Pseudoelement.pseudo_exact_of_exact, CategoryTheory.Abelian.Pseudoelement.sub_of_eq_image]
  E1: auto
families: []
requires: [V05, V07, V24.C04, V24.C08, V25.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Pseudoelements and the diagram lemmas

### Overview

In a category of modules, a diagram lemma is proved by a *diagram chase*: take an element, push it along the arrows, lift it back where exactness allows, and compare. An object of an abelian category has no elements, but the chase still works. The trick is to replace an element of $Y$ by a morphism $y : A \to Y$ from an arbitrary object, and to allow a lift to exist only after precomposition with an epimorphism. This is the method of *refinements*. Mathlib uses it for the four and five lemmas. An older method, *pseudoelements*, takes equivalence classes of such morphisms. This section proves the basic rules of refinements, the four lemma and the five lemma, and works out the snake lemma for $\mathbb{Z}$-modules. The general snake lemma is part of homological algebra, Volume 26.

In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`. The category $C$ is abelian.

### Definitions

**Definition (Exactness at a point).** A pair $X \xrightarrow{f} Y \xrightarrow{g} Z$ with $g \circ f = 0$ is *exact* if the map $f' : X \to \ker g$ with $\ker(g) \circ f' = f$ is an epimorphism.

By the previous section, $f = \ker(g) \circ f'$ is then an epi-mono factorization of $f$, so $\mathrm{im}\, f \cong \ker g$ over $Y$. Conversely, if $\mathrm{im}\, f = \ker g$ as subobjects, then $f'$ is the epimorphism $X \to \mathrm{im}\, f$. So the definition agrees with the form $\mathrm{im}\, f = \ker g$ of Volume 24. A longer sequence is exact if it is exact at each inner object.

**Definition (Refinement).** Let $y : A \to Y$ and $f : X \to Y$. A *lift of $y$ along $f$ up to refinement* is an epimorphism $\pi : A' \to A$ and a map $x : A' \to X$ with $y \circ \pi = f \circ x$.

The object $A$ plays the part of a set of parameters, and $\pi$ is a change of parameters that loses no information, because it is epi.

**Definition (Pseudoelement).** Two maps $a : A \to X$ and $b : B \to X$ are *pseudo-equal* if there are epimorphisms $u : T \to A$ and $v : T \to B$ with $a \circ u = b \circ v$. A *pseudoelement* of $X$ is a class of this equivalence relation. A morphism $f : X \to Y$ sends the class of $a$ to the class of $f \circ a$.

That pseudo-equality is transitive needs the previous section: the pullback of an epimorphism is an epimorphism.

### Theorems and proofs

**Theorem (Epimorphisms are surjective up to refinement).** A map $f : X \to Y$ is an epimorphism if and only if each $y : A \to Y$ has a lift along $f$ up to refinement.

*Proof.* Let $f$ be epi and $y : A \to Y$. Let $A' = A \times_Y X$, with projections $\pi : A' \to A$ and $x : A' \to X$, so that $y \circ \pi = f \circ x$. The map $\pi$ is a pullback of the epimorphism $f$, so it is epi by the previous section. Conversely, apply the condition to $y = 1_Y$. It gives an epimorphism $\pi$ and a map $x$ with $\pi = f \circ x$. If $a \circ f = b \circ f$, then $a \circ \pi = b \circ \pi$, and $\pi$ is epi, so $a = b$. $\square$

The rule for monomorphisms needs no refinement: $f$ is mono if and only if $f \circ x = 0$ implies $x = 0$ for each $x : A \to X$. This is the definition of mono in a preadditive category.

**Corollary (Exactness up to refinement).** Let $g \circ f = 0$. The pair $X \xrightarrow{f} Y \xrightarrow{g} Z$ is exact if and only if for each $y : A \to Y$ with $g \circ y = 0$ there are an epimorphism $\pi : A' \to A$ and a map $x : A' \to X$ with $y \circ \pi = f \circ x$.

*Proof.* Let $k = \ker g$. Maps $y : A \to Y$ with $g \circ y = 0$ are in bijection with maps $y' : A \to \ker g$, by $y = k \circ y'$. Since $k$ is mono, $y' \circ \pi = f' \circ x$ holds if and only if $y \circ \pi = k \circ f' \circ x = f \circ x$. So the condition says that $f'$ is surjective up to refinement, and the theorem says that this is the case if and only if $f'$ is epi. $\square$

In a chase, these two rules replace "choose a preimage" and "an element of the kernel comes from the left". A refinement is a finite step, and a finite chain of epimorphisms composes to an epimorphism. Each chase below ends with a statement of the form $c \circ \pi = 0$ with $\pi$ epi, from which $c = 0$.

**Theorem (Four lemma, mono form).** Consider a commutative diagram with rows $A \xrightarrow{f} B \xrightarrow{g} C \xrightarrow{h} D$ and $A' \xrightarrow{f'} B' \xrightarrow{g'} C' \xrightarrow{h'} D'$ and vertical maps $\alpha, \beta, \gamma, \delta$. Let the top row be exact at $C$ with $g \circ f = 0$, and the bottom row exact at $B'$. If $\alpha$ is epi and $\beta$ and $\delta$ are mono, then $\gamma$ is mono.

*Proof.* Let $c : T \to C$ with $\gamma \circ c = 0$. It suffices to prove $c = 0$.

1. $\delta \circ h \circ c = h' \circ \gamma \circ c = 0$, and $\delta$ is mono, so $h \circ c = 0$.
2. By exactness of the top row at $C$, there are an epimorphism $\pi_1 : T_1 \to T$ and $b : T_1 \to B$ with $c \circ \pi_1 = g \circ b$.
3. Then $g' \circ \beta \circ b = \gamma \circ g \circ b = \gamma \circ c \circ \pi_1 = 0$. By exactness of the bottom row at $B'$, there are an epimorphism $\pi_2 : T_2 \to T_1$ and $a' : T_2 \to A'$ with $\beta \circ b \circ \pi_2 = f' \circ a'$.
4. Since $\alpha$ is epi, there are an epimorphism $\pi_3 : T_3 \to T_2$ and $a : T_3 \to A$ with $a' \circ \pi_3 = \alpha \circ a$.
5. Then $\beta \circ f \circ a = f' \circ \alpha \circ a = f' \circ a' \circ \pi_3 = \beta \circ b \circ \pi_2 \circ \pi_3$. As $\beta$ is mono, $f \circ a = b \circ \pi_2 \circ \pi_3$.
6. Put $\pi = \pi_1 \circ \pi_2 \circ \pi_3$, an epimorphism. Then $c \circ \pi = g \circ b \circ \pi_2 \circ \pi_3 = g \circ f \circ a = 0$, so $c = 0$. $\square$

**Theorem (Four lemma, epi form).** Consider a commutative diagram with exact rows $B \to C \to D \to E$ and $B' \to C' \to D' \to E'$ and vertical maps $\beta, \gamma, \delta, \varepsilon$. If $\beta$ and $\delta$ are epi and $\varepsilon$ is mono, then $\gamma$ is epi.

*Proof.* In $C^{\mathrm{op}}$, which is abelian by the previous section, the diagram reverses. The rows become exact rows $E' \to D' \to C' \to B'$ and $E \to D \to C \to B$, the vertical maps reverse, epimorphisms become monomorphisms, and the mono form applies to $\gamma^{\mathrm{op}}$. So $\gamma^{\mathrm{op}}$ is mono, and $\gamma$ is epi. $\square$

Mathlib proves the epi form directly with refinements, since the duality needs more facts about diagrams in the opposite category. The direct proof is Exercise 4.

**Theorem (Five lemma).** Consider a commutative diagram with exact rows $A \to B \to C \to D \to E$ and $A' \to B' \to C' \to D' \to E'$ and vertical maps $\alpha, \beta, \gamma, \delta, \varepsilon$. If $\alpha$ is epi, $\beta$ and $\delta$ are isomorphisms and $\varepsilon$ is mono, then $\gamma$ is an isomorphism.

*Proof.* The mono form on the first four columns gives that $\gamma$ is mono. The epi form on the last four columns gives that $\gamma$ is epi. A map that is mono and epi in an abelian category is an isomorphism. $\square$

**Theorem (Pseudoelements, stated).** For pseudoelements: $f$ is zero if and only if it sends each pseudoelement to $0$; $f$ is epi if and only if it is surjective on pseudoelements; $f$ is mono if and only if it is injective on pseudoelements; a pair $(f, g)$ with $g f = 0$ is exact if and only if each pseudoelement with $g(y) = 0$ is $f(x)$ for some $x$. Pseudoelements do not form a group, and a map is not determined by its action on them.

The proofs are the arguments above in another language: the surjectivity of an epimorphism is the theorem on refinements.

### Examples

**Example (The snake lemma for $\mathbb{Z}$-modules).** Consider a commutative diagram of abelian groups with exact rows $A \xrightarrow{f} B \xrightarrow{g} C \to 0$ and $0 \to A' \xrightarrow{f'} B' \xrightarrow{g'} C'$, and vertical maps $a, b, c$. The snake lemma gives an exact sequence
$$\ker a \to \ker b \to \ker c \xrightarrow{\partial} \mathrm{coker}\, a \to \mathrm{coker}\, b \to \mathrm{coker}\, c.$$
The map $\partial$ is the head of the snake. Let $z \in \ker c$. Since $g$ is onto, choose $y \in B$ with $g(y) = z$. Then $g'(b(y)) = c(g(y)) = c(z) = 0$, so $b(y) = f'(x')$ for a unique $x' \in A'$, because $f'$ is injective. Put $\partial z = x' + a(A)$.

The class does not depend on the choice of $y$. Another choice is $y + f(x)$ with $x \in A$, by exactness at $B$. It changes $b(y)$ by $b(f(x)) = f'(a(x))$, so it changes $x'$ by $a(x)$, which is zero in $\mathrm{coker}\, a$. The map $\partial$ is additive, because sums of choices are choices.

Exactness at $\ker c$: if $z = g(y)$ with $y \in \ker b$, then $x' = 0$, so $\partial z = 0$. Conversely, if $\partial z = 0$, then $x' = a(x)$ for some $x \in A$. Then $y - f(x)$ is a lift of $z$, and $b(y - f(x)) = f'(x') - f'(a(x)) = 0$. So $z$ comes from $\ker b$.

Exactness at $\mathrm{coker}\, a$: the image of $\partial z$ in $\mathrm{coker}\, b$ is the class of $f'(x') = b(y)$, which is zero. Conversely, if $f'(x') = b(y)$ for some $y \in B$, then $z = g(y)$ satisfies $c(z) = g'(b(y)) = g'(f'(x')) = 0$, and $\partial z$ is the class of $x'$. Exactness at $\ker b$ and at $\mathrm{coker}\, b$ is a direct check, Exercise 5.

**Example (Multiplication by $n$).** Let $m, n \geq 1$ and $d = \gcd(m, n)$. Take both rows equal to $0 \to \mathbb{Z} \xrightarrow{m} \mathbb{Z} \to \mathbb{Z}/m \to 0$, and all vertical maps multiplication by $n$. The kernels are $0$, $0$ and the subgroup of $\mathbb{Z}/m$ killed by $n$, which is cyclic of order $d$. The cokernels are $\mathbb{Z}/n$, $\mathbb{Z}/n$ and $\mathbb{Z}/d$. The snake sequence is $0 \to 0 \to \mathbb{Z}/d \xrightarrow{\partial} \mathbb{Z}/n \xrightarrow{m} \mathbb{Z}/n \to \mathbb{Z}/d \to 0$. For $m = 4$, $n = 6$, the element $z = 2$ of $\mathbb{Z}/4$ lifts to $y = 2$, then $6 y = 12 = 4 \cdot 3$, so $\partial z = 3 \in \mathbb{Z}/6$. The kernel of multiplication by $4$ on $\mathbb{Z}/6$ is $\{0, 3\}$, the image of $\partial$, as exactness requires.

### The library around it

::: mathlib

`CategoryTheory.Abelian.mono_of_epi_of_mono_of_mono` · `Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four`

The mono form of the four lemma. A row is an object of `ComposableArrows C 3`, a diagram is a morphism `φ` between two rows, and `app' φ i` is the vertical map at position `i`. Exactness is `ComposableArrows.Exact`. The epi form is `epi_of_epi_of_epi_of_mono` and the five lemma is `isIso_of_epi_of_isIso_of_isIso_of_mono`, on `ComposableArrows C 4`.

<?decl CategoryTheory.Abelian.mono_of_epi_of_mono_of_mono?>
:::

::: mathlib

`CategoryTheory.epi_iff_surjective_up_to_refinements` · `Mathlib.CategoryTheory.Abelian.Refinements`

The criterion `Epi f ↔ ∀ y : A ⟶ Y, ∃ A' (π : A' ⟶ A) (_ : Epi π) (x : A' ⟶ X), π ≫ y = x ≫ f`. For a short complex `S`, `ShortComplex.exact_iff_exact_up_to_refinements` is the corollary on exactness. The file has the same criteria for maps in homology.

<?decl CategoryTheory.epi_iff_surjective_up_to_refinements?>
:::

::: mathlib

`CategoryTheory.ShortComplex.SnakeInput` · `Mathlib.Algebra.Homology.ShortComplex.SnakeLemma`

The general snake lemma in an abelian category, with the connecting map `SnakeInput.δ`. It belongs to Volume 26.

<?decl CategoryTheory.ShortComplex.SnakeInput?>
:::

Common errors of a learner:

- The pseudoelement coercions are local instances. A proof must enable them with `attribute [local instance] Pseudoelement.objectToSort Pseudoelement.homToFun`. New Mathlib code uses refinements instead.
- `ShortComplex.Exact` is a property of a short complex, not of two arbitrary maps. Build the complex with `ShortComplex.mk f g w` from the proof `w : f ≫ g = 0`.

### Exercises

1. (A) Prove that pseudo-equality is an equivalence relation. *Hint:* for transitivity, use a pullback of an epimorphism.
2. (A) Show that the composite of two epimorphisms is an epimorphism, and use it to justify the last step of the chase in the four lemma.
3. (B) Deduce the short five lemma: in a map of short exact sequences $0 \to A \to B \to C \to 0$ whose outer vertical maps are isomorphisms, the middle vertical map is an isomorphism.
4. (B) Prove the epi form of the four lemma directly with refinements. *Hint:* start with $c' : T \to C'$ and use that $\delta$ is epi.
5. (B) Complete the proof of the snake lemma for $\mathbb{Z}$-modules: show that the maps between kernels and between cokernels are well defined, and prove exactness at $\ker b$ and at $\mathrm{coker}\, b$.
6. (C) Prove the snake lemma in an abelian category with refinements. Define $\partial$ with a pullback of $g$ along $\ker c \to C$ and a pushout of $f'$ along $A' \to \mathrm{coker}\, a$, and check that it is independent of choices.

### Notes and history

The pseudoelements are from Mac Lane's *Homology* and from Freyd's book on abelian categories, and the Mathlib file follows the second volume of Borceux. The refinement method is in unpublished notes of George Bergman, as the Mathlib file says, and its use for exactness proofs in Mathlib is the work of Joël Riou. The snake lemma is old; its name comes from the shape of the connecting map in the usual picture.

The Mathlib files are by Markus Himmel (pseudoelements), Markus Himmel and Joël Riou (the four and five lemmas) and Joël Riou (refinements).

### Reference

<?reference?>
