---
title: The Eilenberg-Steenrod axioms
kind: theory
modules:
  - Mathlib.AlgebraicTopology.EilenbergSteenrod
  - Mathlib.Topology.Category.TopPair
explains:
  E3: [TopPair, TopPair.Homotopy, TopPair.IsExcisive, TopPair.HomologyPretheory, TopPair.HomologyPretheory.IsHomotopyInvariant, TopPair.HomologyPretheory.HasExcisionIso, TopPair.HomologyPretheory.IsAdditive, TopPair.HomologyPretheory.HasPairSequence, TopPair.HomologyPretheory.HasDimensionAxiom, TopPair.HomologyPretheory.IsEilenbergSteenrod]
  E2: [TopPair.fst, TopPair.snd, TopPair.map, TopPair.of, TopPair.ofSubset, TopPair.ofTopCat, TopPair.ofHom, TopPair.Hom.fst, TopPair.Hom.snd, TopPair.Hom.w, TopPair.proj₁, TopPair.proj₂, TopPair.incl, TopPair.diag, TopPair.inclAdjProj₁, TopPair.proj₁AdjDiag, TopPair.j, TopPair.Homotopy.refl, TopPair.Homotopy.symm, TopPair.Homotopy.trans, TopPair.Homotopy.comp, TopPair.Homotopic, TopPair.Homotopic.equivalence, TopPair.isExcisive, TopPair.HomologyPretheory.Hₚ, TopPair.HomologyPretheory.H, TopPair.HomologyPretheory.iso, TopPair.HomologyPretheory.δ, TopPair.HomologyPretheory.shape_δ, TopPair.HomologyPretheory.Hom, TopPair.HomologyPretheory.hFstToHₚ, TopPair.HomologyPretheory.hₚFunctor, TopPair.HomologyPretheory.hFunctor, TopPair.HomologyPretheory.HasPairSequence.exact_pair, TopPair.HomologyPretheory.HasPairSequence.exact_snd, TopPair.HomologyPretheory.HasPairSequence.exact_fst, TopPair.HomologyPretheory.HasDimensionAxiom.isZero_pUnit_of_gt_zero, TopPair.HomologyPretheory.IsExtraordinaryEilenbergSteenrod, TopPair.HomologyPretheory.isEilenbergSteenrod, TopPair.HomologyPretheory.isHomotopyInvariant]
  E1: auto
families: []
requires: [V13.C01, V13.C06, V24.C02, V24.C04, V24.C05, V25.C02, V25.C03, V26.C02, V27.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Eilenberg-Steenrod axioms

### Overview

Section 1 built singular homology from simplices. Many other homology theories of spaces exist: cellular homology, Čech homology, and generalized theories such as bordism and K-homology. Eilenberg and Steenrod found a short list of properties that a homology theory of pairs of spaces must have, and they showed that for finite CW complexes these properties determine the theory from its value on a point. The list has five items: functoriality with a boundary map, homotopy invariance, exactness, excision and the dimension axiom. A sixth axiom, additivity, extends the uniqueness to infinite complexes.

Mathlib states these axioms. It defines the category of topological pairs, homotopies of pairs and excisive maps, bundles the data of a theory as a structure `TopPair.HomologyPretheory`, and gives one class for each axiom. It proves that each axiom is invariant under isomorphism of theories. This section explains the definitions, and it derives from the axioms some first consequences with full proofs. Mathlib does not prove these consequences, and it does not yet prove that singular homology satisfies the axioms. The section says exactly which parts are in the index.

The target category $C$ has zero morphisms in the definitions. In the proofs $C$ is abelian, so that exactness has its usual meaning.

### Definitions

**Definition (Topological pair).** A *topological pair* $(X, A)$ is a space $X$ with a subspace $A$. Mathlib allows any embedding $A \to X$ in place of the inclusion of a subset. A map of pairs $(X, A) \to (Y, B)$ is a continuous map $f : X \to Y$ and a continuous map $A \to B$ that agrees with $f$ on $A$. Equivalently, it is a commutative square.

::: mathlib
`TopPair` · `Mathlib.Topology.Category.TopPair`

`TopPair` is the full subcategory of the arrow category of `TopCat` on the embeddings. For `X : TopPair`, the big space is `X.fst`, the subspace is `X.snd`, and `X.map : X.snd ⟶ X.fst` is the embedding. The constructors are `TopPair.of`, `TopPair.ofSubset` for a subset, and `TopPair.ofTopCat X` for the pair $(X, \emptyset)$.

<?decl TopPair?>
:::

Three functors link pairs and spaces. The functor `TopPair.incl` sends $X$ to $(X, \emptyset)$, `TopPair.proj₁` sends $(X, A)$ to $X$, and `TopPair.proj₂` sends it to $A$. The functor `TopPair.diag` sends $X$ to $(X, X)$. There are adjunctions $\mathrm{incl} \dashv \mathrm{proj}_1 \dashv \mathrm{diag}$, and the map `TopPair.j X` is the map of pairs $(X, \emptyset) \to (X, A)$ given by the identity of $X$.

**Definition (Homotopy of pairs).** A *homotopy* between maps of pairs $f, g : (X, A) \to (Y, B)$ is a homotopy $F : X \times I \to Y$ from $f$ to $g$ together with a homotopy $A \times I \to B$ between the restrictions, compatible with the embeddings. So $F(a, t) \in B$ for all $a \in A$ and $t \in I$.

::: mathlib
`TopPair.Homotopy` · `Mathlib.Topology.Category.TopPair`

A structure with fields `fst` and `snd`, two homotopies in the sense of `TopCat.Homotopy`, and a field `w` for the compatibility. The operations `refl`, `symm`, `trans` and `comp` make `TopPair.Homotopic` an equivalence relation, `TopPair.Homotopic.equivalence`, compatible with composition.

<?decl TopPair.Homotopy?>
:::

**Definition (Excisive map).** Let $(X, A)$ be a pair and $U \subseteq A$ with $\overline{U} \subseteq \operatorname{int} A$. The inclusion $(X \setminus U, A \setminus U) \to (X, A)$ is the excision map. Mathlib phrases this without $U$: a map of pairs $g : (V, D) \to (X, A)$ is *excisive* if $g$ is an embedding of $V$ into $X$, if $g(D) = g(V) \cap A$, and if the closure of the complement of $g(V)$ lies in the interior of $A$. The complement of $g(V)$ plays the role of $U$.

::: mathlib
`TopPair.IsExcisive` · `Mathlib.Topology.Category.TopPair`

The class with the three fields `isEmbedding_fst`, `range_fst_map` and `closure_range_fst_compl`. The class of all excisive maps as a morphism property is `TopPair.isExcisive`.

<?decl TopPair.IsExcisive?>
:::

**Definition (Homology pretheory).** Let $c$ be a complex shape on an index type $\iota$, as in Volume 26. A *homology pretheory* with values in $C$ consists of:

1. a functor $H_i : \mathrm{TopPair} \to C$ for each $i$, the relative homology;
2. a functor $H_i : \mathrm{TopCat} \to C$ for each $i$, the absolute homology, with an isomorphism $H_i(X) \cong H_i(X, \emptyset)$ natural in $X$;
3. a natural map $\delta_{ij} : H_i(X, A) \to H_j(A)$ for all $i, j$, which is $0$ unless $c.\mathrm{Rel}\ i\ j$.

For ordinary homology $c$ is `ComplexShape.down ℕ`, so $c.\mathrm{Rel}\ i\ j$ means $j + 1 = i$, and the only boundary maps are $\partial : H_{n+1}(X, A) \to H_n(A)$.

::: mathlib
`TopPair.HomologyPretheory` · `Mathlib.AlgebraicTopology.EilenbergSteenrod`

The fields are `Hₚ i : TopPair ⥤ C`, `H i : TopCat ⥤ C`, `iso i : H i ≅ incl ⋙ Hₚ i`, `δ i j : Hₚ i ⟶ proj₂ ⋙ H j` and `shape_δ`. A morphism of pretheories, `TopPair.HomologyPretheory.Hom`, is a family of natural maps that commute with `iso` and `δ`. The map $H_i(X) \to H_i(X, A)$ is `hFstToHₚ i X`.

<?decl TopPair.HomologyPretheory?>
:::

**Definition (The axioms).** A homology pretheory $H$ is:

1. *homotopy invariant* if homotopic maps of pairs induce the same map on each $H_i$;
2. *excisive* if each excisive map of pairs induces an isomorphism on each $H_i$;
3. *additive* if each absolute $H_i$ preserves coproducts of spaces;
4. *exact* if for each pair $(X, A)$ the sequence
$$\cdots \to H_i(A) \to H_i(X) \to H_i(X, A) \xrightarrow{\delta_{ij}} H_j(A) \to H_j(X) \to \cdots$$
is exact at each place, and $H_i(X) \to H_i(X, A)$ is an epimorphism when $i$ has no successor in $c$;
5. for $c$ the shape `ComplexShape.down ℕ`, it satisfies the *dimension axiom* if $H_n(\mathrm{pt}) = 0$ for $n \ne 0$.

A theory with the first four properties is an *extraordinary* or generalized homology theory. With the fifth one as well, it is an *Eilenberg-Steenrod homology theory*, or an ordinary homology theory.

::: mathlib
`TopPair.HomologyPretheory.HasPairSequence` · `Mathlib.AlgebraicTopology.EilenbergSteenrod`

The exactness axiom as three fields, `exact_fst`, `exact_pair` and `exact_snd`, one for each kind of place in the sequence, each stated with `ComposableArrows.mk₂`. A fourth field, `epi_map_of_not_rel`, asks that `(HP.Hₚ i).map X.j` be an epimorphism when `i` has no successor.

<?decl TopPair.HomologyPretheory.HasPairSequence?>
:::

::: mathlib
`TopPair.HomologyPretheory.IsEilenbergSteenrod` · `Mathlib.AlgebraicTopology.EilenbergSteenrod`

The class that extends `IsExtraordinaryEilenbergSteenrod` (the classes `IsHomotopyInvariant`, `HasExcisionIso`, `IsAdditive` and `HasPairSequence`) by `HasDimensionAxiom`. Each class has a twin of type `ObjectProperty`, such as `TopPair.HomologyPretheory.isEilenbergSteenrod`, for use with the closure results.

<?decl TopPair.HomologyPretheory.IsEilenbergSteenrod?>
:::

### Theorems and proofs

The first result is the only kind of theorem that Mathlib proves about the axioms.

**Proposition (Invariance under isomorphism).** Let $e : H \cong H'$ be an isomorphism of homology pretheories. If $H$ satisfies one of the axioms, then $H'$ satisfies it too.

*Proof.* Take homotopy invariance. An isomorphism gives natural isomorphisms $e_i : H_i \cong H'_i$ on pairs. For homotopic $f, g$, naturality gives $H'_i(f) = e_i \circ H_i(f) \circ e_i^{-1}$ and the same for $g$, so $H_i(f) = H_i(g)$ implies $H'_i(f) = H'_i(g)$. For excision, $H'_i(g) = e_i \circ H_i(g) \circ e_i^{-1}$ is an isomorphism when $H_i(g)$ is. For additivity, a functor isomorphic to a functor that preserves coproducts also preserves them. For exactness, the isomorphisms $e$ commute with the maps of the sequence, because a morphism of pretheories commutes with $\delta$ and with the isomorphisms $H_i(X) \cong H_i(X, \emptyset)$. An isomorphism of sequences preserves exactness. For the dimension axiom, an object isomorphic to a zero object is zero. $\square$

::: mathlib
`TopPair.HomologyPretheory.isHomotopyInvariant` · `Mathlib.AlgebraicTopology.EilenbergSteenrod`

The property of pretheories, with an instance of `IsClosedUnderIsomorphisms`. Each of the six properties has such an instance, and these instances are the consequences of the axioms that the index of this edition contains.

<?decl TopPair.HomologyPretheory.isHomotopyInvariant?>
:::

The next results are classical. Assume $C$ abelian and $c$ the shape `ComplexShape.down ℕ`.

**Proposition (The pair of a space with itself).** If $H$ is exact, then $H_n(X, X) = 0$ for each space $X$ and each $n$.

*Proof.* In the sequence of $(X, X)$ the map $H_n(A) \to H_n(X)$ is the identity of $H_n(X)$. Exactness at $H_n(X)$ says that the kernel of $j : H_n(X) \to H_n(X, X)$ is the image of the identity, so $j = 0$. Exactness at $H_n(X, X)$ says that the kernel of $\partial : H_n(X,X) \to H_{n-1}(X)$ is the image of $j$, which is $0$, so $\partial$ is a monomorphism. Exactness at $H_{n-1}(A)$ says that the image of $\partial$ is the kernel of the identity, which is $0$, so $\partial = 0$. A monomorphism that is zero has a zero source, so $H_n(X, X) = 0$ for $n \ge 1$. For $n = 0$, the epimorphism axiom says that $j : H_0(X) \to H_0(X, X)$ is onto, and $j = 0$, so $H_0(X, X) = 0$. $\square$

**Proposition (The empty space).** If $H$ is additive, then $H_n(\emptyset) = 0$ for each $n$.

*Proof.* The empty space is the coproduct of the empty family. A functor that preserves this coproduct sends it to an initial object of $C$. In an abelian category an initial object is a zero object. $\square$

**Proposition (Homotopy equivalence).** If $H$ is homotopy invariant and $f : X \to Y$ is a homotopy equivalence of spaces, then $H_n(f)$ is an isomorphism for each $n$.

*Proof.* Let $g$ be a homotopy inverse, so $g f \simeq \mathrm{id}_X$ and $f g \simeq \mathrm{id}_Y$. A homotopy $F$ of maps of spaces gives a homotopy of the pairs $(X, \emptyset) \to (Y, \emptyset)$, with the empty homotopy on the second part. So $H_n(g) H_n(f) = H_n(gf) = H_n(\mathrm{id}) = \mathrm{id}$ on $H_n(X, \emptyset)$, and the same holds for $fg$. Transport along the isomorphisms $H_n(X) \cong H_n(X, \emptyset)$. $\square$

**Corollary (Contractible spaces).** If $H$ is homotopy invariant and satisfies the dimension axiom, then $H_n(X) = 0$ for each contractible space $X$ and each $n \ge 1$, and $H_0(X) \cong H_0(\mathrm{pt})$.

*Proof.* The map $X \to \mathrm{pt}$ is a homotopy equivalence, so $H_n(X) \cong H_n(\mathrm{pt})$, which is $0$ for $n \ge 1$. $\square$

**Theorem (Disk and sphere).** Let $H$ be homotopy invariant and exact with the dimension axiom. Let $D^k$ be the closed disk and $S^{k-1}$ its boundary sphere, $k \ge 1$. Then $\partial : H_n(D^k, S^{k-1}) \to H_{n-1}(S^{k-1})$ is an isomorphism for $n \ge 2$, and $H_1(D^k, S^{k-1})$ is the kernel of $H_0(S^{k-1}) \to H_0(D^k)$.

*Proof.* The disk is convex, so it is contractible by the straight-line homotopy of Chapter 1. By the corollary $H_m(D^k) = 0$ for $m \ge 1$. Write the sequence of the pair around $H_n(D^k, S^{k-1})$:
$$H_n(D^k) \to H_n(D^k, S^{k-1}) \xrightarrow{\partial} H_{n-1}(S^{k-1}) \to H_{n-1}(D^k).$$
For $n \ge 2$ both outer terms are $0$. Exactness at the second term makes $\partial$ a monomorphism, and exactness at the third term makes $\partial$ an epimorphism, so $\partial$ is an isomorphism. For $n = 1$ the left term is still $0$, so $\partial$ is a monomorphism onto the kernel of $H_0(S^{k-1}) \to H_0(D^k)$. $\square$

Excision then identifies $H_n(D^k, S^{k-1})$ with $H_n(S^k, \mathrm{pt})$, and induction gives $H_n(S^k) \cong H_0(\mathrm{pt})$ for $n = k$ and $n = 0$ and $0$ otherwise, for $k \ge 1$. That step needs a good choice of excisive map and is left to Exercise 6.

### Examples

**Example (The interval and its ends).** Take $k = 1$, so $D^1 = [-1, 1]$ and $S^0 = \{-1, 1\}$. Let $R = H_0(\mathrm{pt})$. By additivity $H_0(S^0) = R \oplus R$, and by the corollary $H_0(D^1) \cong R$. Each point of $S^0$ goes into $D^1$, and the composite $\mathrm{pt} \to D^1 \to \mathrm{pt}$ is the identity, so $H_0(\mathrm{pt}) \to H_0(D^1)$ is the inverse of the isomorphism $H_0(D^1) \to H_0(\mathrm{pt})$. So the map $H_0(S^0) \to H_0(D^1) \cong R$ is $(a, b) \mapsto a + b$. Its kernel is $\{(a, -a)\} \cong R$, so $H_1(D^1, S^0) \cong R$. The next term $H_0(D^1, S^0)$ is the cokernel of the map $(a, b) \mapsto a + b$, which is onto, so $H_0(D^1, S^0) = 0$.

**Example (An excisive map).** Let $X = [0, 3]$, $A = [1, 3]$ and $U = [2, 3]$. Then $\overline{U} = [2,3]$ lies in $\operatorname{int} A = (1, 3]$, the interior in $X$. The inclusion $g : ([0, 2), [1, 2)) \to ([0, 3], [1, 3])$ is excisive: it is an embedding, $g([1,2)) = [0, 2) \cap [1, 3]$, and the closure of the complement $[2, 3]$ lies in $(1, 3]$. If $U = [1, 3] = A$ instead, the closure of $U$ is $[1, 3]$ and $1$ is not an interior point of $A$, so the condition fails.

**Example (Singular homology, as far as the index goes).** Section 1 gives absolute singular homology as the functors `singularHomologyFunctor C n`. Three of the axioms for absolute homology are there. Homotopy invariance is `TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor`. The dimension axiom follows from `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`, since a point is totally disconnected. The value on a point in degree $0$ is $R$. The index of this edition has no declaration for relative singular homology of a pair in `TopPair`, and no declaration that makes singular homology a `TopPair.HomologyPretheory`. So it has no proof of excision for singular homology.

**Example (A Lean statement).** The dimension axiom can be used through the instance that the class `IsEilenbergSteenrod` provides.

```lean
open CategoryTheory Limits TopPair in
example {C : Type*} [Category C] [Preadditive C]
    (HP : HomologyPretheory.{0} C (ComplexShape.down ℕ)) [HP.IsEilenbergSteenrod]
    (n : ℕ) (hn : n ≠ 0) : IsZero ((HP.H n).obj (TopCat.of PUnit)) :=
  HomologyPretheory.HasDimensionAxiom.isZero_pUnit_of_gt_zero n hn
```

### The library around it

The file `TopPair` follows the textbook definitions closely. Two choices differ. A pair is an embedding, not a subset, so the pairs $(X, A)$ and $(X, A')$ with $A \cong A'$ over $X$ are isomorphic objects and not equal ones. The excision condition is stated for a map $g$ and not for a subset $U$, which makes the class `IsExcisive` a morphism property of `TopPair`.

The structure `HomologyPretheory` takes a complex shape $c$. With `ComplexShape.down ℕ` it gives ordinary homology. With `ComplexShape.down ℤ` it can hold a generalized theory with nonzero groups in negative degrees, such as stable homotopy. The dimension axiom is stated only for the shape on $\mathbb{N}$.

::: mathlib
`TopPair.inclAdjProj₁` · `Mathlib.Topology.Category.TopPair`

The adjunction `incl ⊣ proj₁`: a map of pairs $(X, \emptyset) \to (Y, B)$ is the same as a continuous map $X \to Y$. The second adjunction `proj₁AdjDiag` says that a map $X \to Y$ out of the big space is a map of pairs $(X, A) \to (Y, Y)$.

<?decl TopPair.inclAdjProj₁?>
:::

The index of this edition has no declaration for the uniqueness theorem of Eilenberg and Steenrod, for the Mayer-Vietoris sequence derived from the axioms, or for cellular homology.

Common errors of a learner: The first error is to mix up `fst` and `snd`. In `TopPair`, `X.fst` is the big space $X$ and `X.snd` is the subspace $A$, while in the arrow category the subspace is the source, `X.left`. The second error is to expect $\delta$ to be nonzero for all indices. The field `shape_δ` forces $\delta_{ij} = 0$ unless $c.\mathrm{Rel}\ i\ j$. The third error is to read the excision condition with closure in the wrong space. The closure and interior are taken in $X$, not in $A$. The fourth error is to believe that Mathlib already shows that singular homology is an example.

### Exercises

1. (A) Show that the map `TopPair.j X` is an isomorphism of pairs when the subspace of $X$ is empty. *Hint:* both components are identities.
2. (A) Let $H$ be exact. Show that $H_n(X) \to H_n(X, A)$ is an isomorphism for each $n$ when $H_n(A) = 0$ for all $n$. *Hint:* the sequence has zeros on both sides.
3. (A) Let $H$ be homotopy invariant and exact. Show that the inclusion $S^{k-1} \to D^k \setminus \{0\}$ induces an isomorphism on each $H_n$. *Hint:* the radial retraction is a homotopy equivalence.
4. (B) Let $H$ be additive, exact and homotopy invariant with the dimension axiom, and $R = H_0(\mathrm{pt})$. Compute $H_n(X)$ for a discrete space $X$ with $m$ points, $m$ finite. *Hint:* write $X$ as a coproduct.
5. (B) Let $\varphi : H \to H'$ be a morphism of exact pretheories. Assume that $\varphi$ is an isomorphism on the absolute groups $H_n(X)$ for all $X$ and $n$. Show that it is an isomorphism on relative groups. *Hint:* the five lemma on the sequences of a pair.
6. (C) Let $H$ be an ordinary homology theory with $R = H_0(\mathrm{pt})$. Use excision for the pair $(S^k, \text{lower hemisphere})$ and the theorem on disk and sphere to prove $H_k(S^k) \cong R$ for $k \ge 1$. *Hint:* remove a small open cap around the south pole, and use that the upper hemisphere is a disk.
7. (C) Let $H$ be an extraordinary theory on `ComplexShape.down ℤ`. Show that $H'_i = H_{i+1}$ with $\delta'_{ij} = \delta_{i+1, j+1}$ is again an extraordinary theory. If $H_i(\mathrm{pt}) = 0$ for $i \ne 0$, find the one degree in which $H'(\mathrm{pt})$ can be nonzero. *Hint:* the shape relation $j + 1 = i$ is preserved by adding one to both indices.

### Notes and history

Eilenberg and Steenrod announced their axioms in 1945 and gave the full treatment in the book *Foundations of Algebraic Topology* of 1952. The book proves that the axioms determine the homology of finite CW complexes from the coefficient group $H_0(\mathrm{pt})$. Additivity was added later to treat infinite complexes. Theories without the dimension axiom became central in stable homotopy theory, which explains the name extraordinary.

The Mathlib Authors of `AlgebraicTopology.EilenbergSteenrod` and `Topology.Category.TopPair`: Jakob Scharmberg.

### Reference

<?reference?>
