---
title: Generators, simple objects and Noetherian categories
kind: theory
modules:
  - Mathlib.CategoryTheory.Generator.Basic
  - Mathlib.CategoryTheory.Generator.Preadditive
  - Mathlib.CategoryTheory.Simple
  - Mathlib.CategoryTheory.Preadditive.Schur
  - Mathlib.CategoryTheory.Noetherian
explains:
  E3: [CategoryTheory.ObjectProperty.IsSeparating, CategoryTheory.ObjectProperty.IsDetecting, CategoryTheory.IsSeparator, CategoryTheory.isSeparator_iff_faithful_coyoneda_obj, CategoryTheory.ObjectProperty.IsSeparating.isDetecting, CategoryTheory.Simple, CategoryTheory.isIso_of_hom_simple, CategoryTheory.endomorphism_simple_eq_smul_id, CategoryTheory.Noetherian]
  E2: [CategoryTheory.IsCoseparator, CategoryTheory.IsDetector, CategoryTheory.ObjectProperty.IsDetecting.isSeparating, CategoryTheory.isDetector_iff_reflectsIsomorphisms_coyoneda_obj, CategoryTheory.ObjectProperty.isSeparating_iff_epi, CategoryTheory.isSeparator_sigma, CategoryTheory.wellPowered_of_isDetector, CategoryTheory.Preadditive.isSeparator_iff, CategoryTheory.isSeparator_iff_faithful_preadditiveCoyoneda, CategoryTheory.zero_not_simple, CategoryTheory.kernel_zero_of_ne_zero_from_simple, CategoryTheory.mono_of_ne_zero_from_simple, CategoryTheory.epi_of_ne_zero_to_simple, CategoryTheory.isIso_iff_ne_zero, CategoryTheory.simple_of_cosimple, CategoryTheory.indecomposable_of_simple, CategoryTheory.simple_iff_subobject_isSimpleOrder, CategoryTheory.finrank_hom_simple_simple_le_one, CategoryTheory.fieldEndOfFiniteDimensional, CategoryTheory.Artinian]
  E1: auto
families: []
requires: [V06, V07, V11, V24.C01, V24.C03, V24.C04, V24.C08, V25.C01, V25.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Generators, simple objects and Noetherian categories

### Overview

In the category of sets, two functions $f, g : X \to Y$ are equal if they agree on each element, that is, if $f \circ x = g \circ x$ for each map $x$ from the one-point set to $X$. An object $G$ with this property in a general category is a *separator*, or a generator. Separators control the size of a category. With a detector, a category with pullbacks has only a set of subobjects of each object, and the Grothendieck categories of Chapter 2 have enough injectives because they have a separator. The second topic is the opposite end: a *simple* object has no subobjects other than $0$ and itself. Schur's lemma says that each nonzero morphism between simple objects is an isomorphism. The section ends with Noetherian and Artinian categories, in which chains of subobjects stop.

The section uses the properties of objects of Section 1. In the text $g \circ f$ is the textbook composite, and Mathlib writes `f ≫ g`.

### Definitions

**Definition (Separating and detecting).** Let $P$ be a property of objects of a category $C$.

1. $P$ is *separating* if, for all $f, g : X \to Y$ with $f \circ h = g \circ h$ for each $h : G \to X$ with $P(G)$, $f = g$.
2. $P$ is *detecting* if a morphism $f : X \to Y$ is an isomorphism when, for each $G$ with $P(G)$, each $h : G \to Y$ factors as $h = f \circ h'$ for a unique $h' : G \to X$.

An object $G$ is a *separator* if the property "is $G$" is separating, and a *detector* if it is detecting. The duals are *coseparating*, *codetecting*, *coseparator* and *codetector*. They are the same notions in $C^{\mathrm{op}}$.

**Definition (Simple object).** Let $C$ have zero morphisms. An object $X$ is *simple* if, for each monomorphism $f : Y \to X$, $f$ is an isomorphism if and only if $f \neq 0$.

The definition excludes the zero object. If $X = 0$, the zero morphism $0 \to 0$ is a monomorphism and an isomorphism, but it is zero. So $0$ is not simple.

**Definition (Noetherian and Artinian categories).** An object $X$ is *Noetherian* if each increasing chain of subobjects of $X$ is eventually constant, and *Artinian* if each decreasing chain is eventually constant. A category is Noetherian (or Artinian) if it is essentially small and each object is Noetherian (or Artinian).

::: mathlib
`CategoryTheory.ObjectProperty.IsSeparating` · `Mathlib.CategoryTheory.Generator.Basic`

`P.IsSeparating` is the statement `∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ (G : C) (_ : P G) (h : G ⟶ X), h ≫ f = h ≫ g) → f = g`. A single object is a separator by `IsSeparator G`, which is `IsSeparating (.singleton G)`. The class `HasSeparator C` says that some separator exists.

<?decl CategoryTheory.ObjectProperty.IsSeparating?>
:::

### Theorems and proofs

**Theorem (Separators and the Hom functor).** An object $G$ is a separator if and only if the functor $\mathrm{Hom}(G, -) : C \to \mathrm{Set}$ is faithful. It is a detector if and only if $\mathrm{Hom}(G, -)$ reflects isomorphisms.

*Proof.* The map $\mathrm{Hom}(G, f) : \mathrm{Hom}(G, X) \to \mathrm{Hom}(G, Y)$ sends $h$ to $f \circ h$. Two morphisms $f, g$ have the same image under the functor exactly when $f \circ h = g \circ h$ for each $h$, so faithfulness is the definition of a separator. A map of sets is a bijection exactly when each element of the target has a unique preimage. For $\mathrm{Hom}(G, f)$, this says that each $h : G \to Y$ is $f \circ h'$ for a unique $h'$. So $\mathrm{Hom}(G, -)$ reflects isomorphisms exactly when $G$ is a detector. ∎

**Theorem (Coproducts of separators).** Let $C$ have zero morphisms, and let $(G_i)_{i \in I}$ be a family of objects with a coproduct $\coprod_i G_i$ and injections $u_i$. Then $\coprod_i G_i$ is a separator if and only if the family is separating.

*Proof.* Suppose $\coprod_i G_i$ is a separator, and let $f, g : X \to Y$ with $f \circ k = g \circ k$ for each $i$ and each $k : G_i \to X$. For $h : \coprod_i G_i \to X$, the maps $f \circ h$ and $g \circ h$ agree after each $u_i$, since $h \circ u_i$ is such a $k$. By the universal property, $f \circ h = g \circ h$. So $f = g$.

Conversely, suppose the family is separating, and let $f \circ h = g \circ h$ for each $h : \coprod_i G_i \to X$. Let $k : G_i \to X$. Let $h$ be the map with $h \circ u_i = k$ and $h \circ u_j = 0$ for $j \neq i$. Then $f \circ k = f \circ h \circ u_i = g \circ h \circ u_i = g \circ k$. Since the family is separating, $f = g$. ∎

The first part holds in each category. The second part uses the zero morphisms to extend $k$ to all of the coproduct, and Mathlib states it with `HasZeroMorphisms C`. The next theorem uses a different coproduct and needs no zero morphisms.

**Theorem (Separating families and epimorphisms).** Suppose that for each $X$ the coproduct $S_X = \coprod_{(G, h)} G$ over all pairs with $P(G)$ and $h : G \to X$ exists, and let $p_X : S_X \to X$ be the map that is $h$ on the summand of $(G, h)$. Then $P$ is separating if and only if each $p_X$ is an epimorphism.

*Proof.* Suppose $P$ is separating and $f \circ p_X = g \circ p_X$. For each $h : G \to X$ with $P(G)$, $h$ is $p_X$ composed with the injection of the summand $(G, h)$, so $f \circ h = g \circ h$. Thus $f = g$, and $p_X$ is epi. Conversely, suppose each $p_X$ is epi and $f \circ h = g \circ h$ for each $h$. Then $f \circ p_X$ and $g \circ p_X$ agree on each summand, so they are equal, and $f = g$. ∎

So a family is separating when each object is a quotient of a coproduct of its members. In particular, in a category with coproducts, $G$ is a separator if and only if each $X$ is a quotient of a coproduct of copies of $G$.

**Theorem (Separating and detecting).** If $C$ has equalizers, each detecting property is separating. If $C$ is balanced, that is, each morphism that is mono and epi is an isomorphism, each separating property is detecting.

*Proof.* Let $P$ be detecting and $f, g : X \to Y$ with $f \circ h = g \circ h$ for each $h : G \to X$ with $P(G)$. Let $e : E \to X$ be the equalizer of $f$ and $g$. Each such $h$ factors through $e$, and the factorization is unique since $e$ is mono. Since $P$ is detecting, $e$ is an isomorphism, so $f = g$.

Now let $C$ be balanced and $P$ separating. Let $f : X \to Y$ have the unique factorization property. To show that $f$ is mono, let $a, b : Z \to X$ with $f \circ a = f \circ b$. For each $k : G \to Z$ with $P(G)$, the maps $a \circ k$ and $b \circ k$ both factor $f \circ a \circ k$ through $f$. By uniqueness, $a \circ k = b \circ k$. Since $P$ is separating, $a = b$. To show that $f$ is epi, let $c, d : Y \to W$ with $c \circ f = d \circ f$. For $k : G \to Y$, write $k = f \circ k'$. Then $c \circ k = c \circ f \circ k' = d \circ f \circ k' = d \circ k$, so $c = d$. Since $C$ is balanced, $f$ is an isomorphism. ∎

Abelian categories are balanced, so in an abelian category separators and detectors are the same. Mathlib also proves that a category with pullbacks and a detector is well-powered, by `wellPowered_of_isDetector`.

**Theorem (Separators in preadditive categories).** In a preadditive category, $G$ is a separator if and only if, for each $f : X \to Y$ with $f \circ h = 0$ for each $h : G \to X$, $f = 0$.

*Proof.* If $G$ is a separator, apply the definition to $f$ and $0$. Conversely, if $f \circ h = g \circ h$ for each $h$, then $(f - g) \circ h = 0$ for each $h$, so $f - g = 0$. ∎

**Theorem (Basic facts on simple objects).** Let $X$ and $Y$ be simple.

1. If $C$ is preadditive with kernels, each nonzero $f : X \to Z$ is a monomorphism.
2. If $C$ has equalizers and images, each nonzero $f : Z \to Y$ is an epimorphism.
3. (Schur's lemma) If $C$ is preadditive with kernels, each nonzero $f : X \to Y$ is an isomorphism, and $\mathrm{End}(X)$ is a division ring.
4. If $C$ is linear over an algebraically closed field $k$ with kernels and $\mathrm{End}(X)$ is finite-dimensional, then each endomorphism of $X$ is $c \cdot 1_X$ for a unique $c \in k$.

*Proof.* (1) Let $i : K \to X$ be the kernel of $f$. It is a monomorphism. If $i \neq 0$, then $i$ is an isomorphism since $X$ is simple, and $f = f \circ i \circ i^{-1} = 0$, which is false. So $i = 0$, and a morphism with kernel $0$ in a preadditive category is mono: if $f \circ a = f \circ b$, then $f \circ (a - b) = 0$, so $a - b$ factors through $i = 0$ and $a = b$.

(2) Write $f = m \circ e$ with $m : I \to Y$ the image, a monomorphism. If $m = 0$ then $f = 0$. So $m \neq 0$, and $m$ is an isomorphism since $Y$ is simple. The image factorization has $e$ epi when $C$ has equalizers, so $f$ is epi.

(3) By (1), $f$ is mono, and $f \neq 0$, so $f$ is an isomorphism since $Y$ is simple. Then each nonzero element of $\mathrm{End}(X)$ is invertible, and $1_X \neq 0$ since $X$ is not zero. So $\mathrm{End}(X)$ is a division ring.

(4) Let $f \in \mathrm{End}(X)$. The subring $k[f]$ is commutative and finite-dimensional over $k$, and it has no zero divisors, since it sits in a division ring. A finite-dimensional commutative domain over $k$ is a field, by the injectivity of multiplication by a nonzero element. It is a finite extension of $k$, so it is $k$ since $k$ is algebraically closed. So $f = c \cdot 1_X$. The scalar $c$ is unique because $1_X \neq 0$. ∎

Mathlib proves (4) by the spectrum of $f$ in place of $k[f]$: since $k$ is algebraically closed and $\mathrm{End}(X)$ is finite-dimensional, $f$ has an element $c$ in its spectrum, so $f - c \cdot 1_X$ is not invertible, so it is $0$ by (3).

**Theorem (Simple objects by subobjects).** If $C$ has a zero object and zero morphisms, $X$ is simple if and only if the poset of subobjects of $X$ has exactly two elements, $0$ and $X$. In an abelian category, $X$ is simple if and only if, for each epimorphism $f : X \to Z$, $f$ is an isomorphism exactly when $f \neq 0$.

*Proof.* A subobject is a class of monomorphisms $Y \to X$. A monomorphism is zero exactly when $Y$ is a zero object, which gives the bottom subobject, and the simple condition says that the others are equal to the top. For the second claim in an abelian category, a subobject $Y \to X$ gives the epimorphism $X \to X / Y$, and an epimorphism $f$ gives its kernel. These two maps are inverse bijections between subobjects and quotients by Chapter 2. Under them, $Y = 0$ corresponds to $f$ an isomorphism and $Y = X$ to $f = 0$. ∎

### Examples

**Example (Sets, abelian groups and modules).** In the category of sets, the one-point set is a separator and a detector, and the two-point set is a coseparator. In the category of $R$-modules, $R$ is a separator, since $\mathrm{Hom}(R, M) \cong M$. In the category of abelian groups, $\mathbb{Q}/\mathbb{Z}$ is a coseparator: for $x \neq 0$ in $A$, the cyclic group $\langle x \rangle$ has a nonzero map to $\mathbb{Q}/\mathbb{Z}$, and the map extends to $A$ since $\mathbb{Q}/\mathbb{Z}$ is injective. The group $\mathbb{Q}$ is not a separator of abelian groups, since $\mathrm{Hom}(\mathbb{Q}, \mathbb{Z}) = 0$ cannot separate $1_{\mathbb{Z}}$ from $0$.

**Example (Schur's lemma needs the closed field).** The simple abelian groups are the groups $\mathbb{Z}/p$ for $p$ prime, with $\mathrm{End}(\mathbb{Z}/p) = \mathbb{F}_p$. Over the real numbers, let $M = \mathbb{C}$ as a module over $\mathbb{R}[x]$ with $x$ acting by multiplication by $i$. A nonzero $\mathbb{R}[x]$-submodule of $M$ is a real subspace stable under multiplication by $i$, so it is $M$. Thus $M$ is simple, and $\mathrm{End}(M) = \mathbb{C}$, which is a field of dimension 2 over $\mathbb{R}$. So part 4 of the theorem fails when $k$ is not algebraically closed. Over an algebraically closed field, Mathlib also proves that $\mathrm{Hom}(X, Y)$ has dimension at most 1 for simple $X$ and $Y$ with $\mathrm{End}(X)$ finite-dimensional, by `finrank_hom_simple_simple_le_one`.

**Example (Finite abelian groups).** The category of finite abelian groups is essentially small, since each such group is isomorphic to one on a set $\{1, \dots, n\}$. Each finite group has a finite poset of subgroups, so chains stop in both directions. Thus the category is Noetherian and Artinian. The category of finitely generated abelian groups is Noetherian but not Artinian, since $\mathbb{Z} \supset 2\mathbb{Z} \supset 4\mathbb{Z} \supset \cdots$ does not stop.

### The library around it

::: mathlib
`CategoryTheory.Simple` · `Mathlib.CategoryTheory.Simple`

`Simple X` is the class with the one field `mono_isIso_iff_nonzero : ∀ {Y : C} (f : Y ⟶ X) [Mono f], IsIso f ↔ f ≠ 0`. It needs only `HasZeroMorphisms C`. The theorem `zero_not_simple` checks that the zero object is not simple, and `indecomposable_of_simple` gives that a simple object of a preadditive category with binary biproducts is indecomposable.

<?decl CategoryTheory.Simple?>
:::

::: mathlib
`CategoryTheory.endomorphism_simple_eq_smul_id` · `Mathlib.CategoryTheory.Preadditive.Schur`

For a field `𝕜` with `IsAlgClosed 𝕜`, a `𝕜`-linear category with kernels, `Simple X` and `FiniteDimensional 𝕜 (X ⟶ X)`, each `f : X ⟶ X` has `∃ c : 𝕜, c • 𝟙 X = f`. The file also gives the instance `DivisionRing (End X)` and the field structure `fieldEndOfFiniteDimensional`.

<?decl CategoryTheory.endomorphism_simple_eq_smul_id?>
:::

The classes `Noetherian C` and `Artinian C` extend `EssentiallySmall C` and ask for `IsNoetherianObject X` and `IsArtinianObject X` for each object. These object classes are in the folder `Subobject`, and the file `Subobject.ArtinianObject` proves `exists_simple_subobject`: a nonzero Artinian object has a simple subobject. The Jordan-Hölder theorem for abelian categories is a TODO of the file `Noetherian`.

Common errors of a learner:

- `IsSeparator G` in Mathlib is the condition for one object. A family is separating with `ObjectProperty.IsSeparating (.ofObj f)`, and the link with coproducts is `isSeparator_sigma`.
- The hypothesis `[Simple X]` is a class, so Lean finds it by instance search. A proof that $X$ is simple must be given with `haveI` or as an instance before the theorems of this section apply.
- Part 4 of the theorem on simple objects needs `IsAlgClosed 𝕜`. Over other fields only the division ring structure is available.

### Exercises

1. (A) Show that a category with a zero object has the zero object as a separator only if each object is a zero object.
2. (A) Show that a simple object of an abelian category has no quotients other than $0$ and itself.
3. (B) Show that $\bigoplus_p \mathbb{Z}/p$, over all primes, is not a separator of abelian groups, and that $\mathbb{Z}$ is a separator but not a coseparator.
4. (B) Show that the category of abelian groups has no simple projective object.
5. (B) Let $X$ be simple in an abelian category and let $f : X \oplus X \to X \oplus X$ be an endomorphism. Show that $f$ is given by a $2 \times 2$ matrix with entries in the division ring $\mathrm{End}(X)$, and that $f$ is an isomorphism if and only if the matrix is invertible.
6. (C) Let $X$ be a Noetherian and Artinian object of an abelian category. Prove that $X$ has a composition series $0 = X_0 \subset X_1 \subset \cdots \subset X_n = X$ with each $X_i / X_{i-1}$ simple. *Hint:* take a simple subobject of $X / X_{i-1}$ to build $X_i$, and use the Noetherian condition to show that the process stops.

### Notes and history

Generators are in Grothendieck's paper of 1957, in the definition of the categories now named after him, and in Freyd's book *Abelian categories* of 1964, which also uses detectors and coseparators. Schur's lemma is from Schur's work of 1905 on group representations. The Mathlib forms of separators and detectors follow the conventions of the nLab and of Borceux's *Handbook of categorical algebra*.

The Mathlib files are by Markus Himmel (separators and detectors, and the preadditive forms), Markus Himmel and Kim Morrison (simple objects and Schur's lemma) and Kim Morrison (Noetherian and Artinian categories).

### Reference

<?reference?>
