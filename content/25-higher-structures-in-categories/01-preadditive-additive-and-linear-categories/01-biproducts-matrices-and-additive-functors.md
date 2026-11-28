---
title: Biproducts, matrices and additive functors
kind: theory
modules:
  - Mathlib.CategoryTheory.Preadditive.Biproducts
  - Mathlib.CategoryTheory.Preadditive.Mat
  - Mathlib.CategoryTheory.Preadditive.OfBiproducts
  - Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
  - Mathlib.CategoryTheory.Preadditive.HomOrthogonal
explains:
  E3: [CategoryTheory.Limits.isBilimitOfTotal, CategoryTheory.Limits.biproduct.total, CategoryTheory.Limits.HasBiproduct.of_hasProduct, CategoryTheory.Biprod.gaussian, CategoryTheory.Biprod.isoElim, CategoryTheory.SemiadditiveOfBinaryBiproducts.addCommMonoidHomOfHasBinaryBiproducts, CategoryTheory.Mat_, CategoryTheory.Mat_.lift, CategoryTheory.Functor.Additive, CategoryTheory.Functor.preservesFiniteBiproductsOfAdditive]
  E2: [CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts, CategoryTheory.Biprod.ofComponents, CategoryTheory.Biprod.unipotentLower, CategoryTheory.Biprod.column_nonzero_of_iso, CategoryTheory.subsingleton_preadditive_of_hasBinaryBiproducts, CategoryTheory.Limits.biprod.add_eq_lift_id_desc, CategoryTheory.SemiadditiveOfBinaryBiproducts.distrib, CategoryTheory.SemiadditiveOfBinaryBiproducts.add_eq_left_addition, CategoryTheory.Mat_.embedding, CategoryTheory.Mat_.embeddingLiftIso, CategoryTheory.Mat_.equivalenceSelfOfHasFiniteBiproducts, CategoryTheory.Mat, CategoryTheory.Mat.equivalenceSingleObj, CategoryTheory.Functor.map_add, CategoryTheory.Functor.additive_of_preservesBinaryBiproducts, CategoryTheory.AdditiveFunctor]
  E1: auto
families: []
requires: [V05, V07, V24.C02, V24.C04, V24.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Biproducts, matrices and additive functors

### Overview

Volume 24, Chapter 8 defined preadditive categories, binary biproducts and additive functors, and proved that in a preadditive category a binary product is a biproduct. This section takes the theory to finite families. One equation, the *total identity*, detects a finite biproduct. Morphisms between biproducts are matrices, and Gaussian elimination works in any preadditive category. In the other direction, binary biproducts alone fix the addition of morphisms: a category with zero morphisms and binary biproducts has exactly one enrichment in commutative monoids. Last, the category `Mat_ C` of formal finite sums is the free category with finite biproducts on a preadditive category $C$, and additive functors are the functors that preserve biproducts.

In the text, $g \circ f$ is the textbook composite. Mathlib writes it `f ≫ g`. For a family $(X_j)_{j \in J}$ the biproduct is $\bigoplus_j X_j$, with projections $\pi_j$ and inclusions $\iota_j$, and $\delta_{jk}$ is $1$ if $j = k$ and $0$ if not.

### Definitions

**Definition (Bicone and biproduct).** Let $C$ have zero morphisms and let $(X_j)_{j \in J}$ be a family of objects. A *bicone* is an object $P$ with maps $\pi_j : P \to X_j$ and $\iota_j : X_j \to P$ such that $\pi_k \circ \iota_j = \delta_{jk}$. It is a *bilimit* if $(P, \pi)$ is a limit cone and $(P, \iota)$ is a colimit cocone. A *biproduct* is a bilimit bicone.

**Definition (Matrix of a morphism).** Let $\varphi : \bigoplus_j X_j \to \bigoplus_k Y_k$. Its *entries* are $\varphi_{kj} = \pi_k \circ \varphi \circ \iota_j : X_j \to Y_k$. Conversely, a family $m_{kj} : X_j \to Y_k$ gives the morphism `biproduct.matrix m`, which is the unique map with these entries.

For two summands Mathlib has `Biprod.ofComponents f₁₁ f₁₂ f₂₁ f₂₂`, where `fᵢⱼ : Xᵢ ⟶ Yⱼ`, source index first.

**Definition (Additive functor).** A functor $F : C \to D$ between preadditive categories is *additive* if $F(f + g) = F(f) + F(g)$ for all parallel $f, g$.

Then $F(0) = F(0 + 0) = F(0) + F(0)$, so $F(0) = 0$, and $F(-f) = -F(f)$.

::: mathlib

`CategoryTheory.Functor.Additive` · `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`

A class with one field, `map_add`. Additive functors from `C` to `D` form the full subcategory `C ⥤+ D` of the functor category, named `AdditiveFunctor`.

<?decl CategoryTheory.Functor.Additive?>
:::

### Theorems and proofs

From here to the end of the section, $C$ is preadditive and $J$ is finite.

**Theorem (Total identity).** A bicone $(P, \pi, \iota)$ on $(X_j)_{j \in J}$ with $\sum_j \iota_j \circ \pi_j = 1_P$ is a bilimit.

*Proof.* Let $(T, s)$ be a cone with legs $s_j : T \to X_j$. Put $u = \sum_j \iota_j \circ s_j$. Then $\pi_k \circ u = \sum_j \pi_k \circ \iota_j \circ s_j = \sum_j \delta_{jk} s_j = s_k$ by bilinearity of composition. So $u$ is a map of cones. If $m : T \to P$ also has $\pi_k \circ m = s_k$ for all $k$, then $m = 1_P \circ m = \sum_j \iota_j \circ \pi_j \circ m = \sum_j \iota_j \circ s_j = u$. So $(P, \pi)$ is a limit. The proof for the cocone is the dual: for a cocone $t_j : X_j \to T$ the unique map is $\sum_j t_j \circ \pi_j$. $\square$

Conversely, each biproduct satisfies the total identity, by the uniqueness of maps into a limit. Mathlib states this as `biproduct.total`.

**Theorem (Finite products are biproducts).** If the product of $(X_j)_{j \in J}$ exists, then the biproduct exists. Hence a preadditive category with finite products has finite biproducts.

*Proof.* Let $(P, p)$ be a product. For each $k$, let $\iota_k : X_k \to P$ be the unique map with $p_j \circ \iota_k = \delta_{jk}$. Then $(P, p, \iota)$ is a bicone. Put $e = \sum_j \iota_j \circ p_j$. For each $k$, $p_k \circ e = \sum_j \delta_{jk} p_j = p_k = p_k \circ 1_P$. Two maps into a product with the same components are equal, so $e = 1_P$. The total identity theorem completes the proof. $\square$

**Proposition (Matrix multiplication).** Let $\varphi : \bigoplus_j X_j \to \bigoplus_k Y_k$ and $\psi : \bigoplus_k Y_k \to \bigoplus_l Z_l$. Then $(\psi \circ \varphi)_{lj} = \sum_k \psi_{lk} \circ \varphi_{kj}$.

*Proof.* Insert the total identity of $\bigoplus_k Y_k$: $\pi_l \circ \psi \circ \varphi \circ \iota_j = \pi_l \circ \psi \circ (\sum_k \iota_k \pi_k) \circ \varphi \circ \iota_j = \sum_k (\pi_l \psi \iota_k)(\pi_k \varphi \iota_j)$. $\square$

**Theorem (Gaussian elimination).** Let $f : X_1 \oplus X_2 \to Y_1 \oplus Y_2$ have entries $f_{ij} : X_i \to Y_j$, and let $f_{11}$ be an isomorphism. Then there are automorphisms $L$ of $X_1 \oplus X_2$ and $R$ of $Y_1 \oplus Y_2$ such that $R \circ f \circ L = f_{11} \oplus g$ with $g = f_{22} - f_{12} \circ f_{11}^{-1} \circ f_{21}$. If also $f$ is an isomorphism, then $g : X_2 \to Y_2$ is an isomorphism.

*Proof.* Let $L$ have entries $L_{11} = 1$, $L_{12} = 0$, $L_{21} = -f_{11}^{-1} \circ f_{21}$, $L_{22} = 1$, in the source-first order of the definition. Its inverse has $+f_{11}^{-1} \circ f_{21}$ in place of the third entry. Let $R$ have entries $R_{11} = 1$, $R_{12} = -f_{12} \circ f_{11}^{-1}$, $R_{21} = 0$, $R_{22} = 1$, again invertible.  The entry $X_2 \to Y_1$ of $f \circ L$ is $f_{21} - f_{11} \circ f_{11}^{-1} \circ f_{21} = 0$. The entry $X_1 \to Y_2$ of $R \circ f$ is $f_{12} - f_{12} \circ f_{11}^{-1} \circ f_{11} = 0$. The two other entries of $R \circ f \circ L$ are $f_{11}$ and $f_{22} - f_{12} f_{11}^{-1} f_{21}$, by the same calculation. For the last claim, let $h = f_{11} \oplus g$. It is an isomorphism, as a composite of isomorphisms. Let $k = \pi_2 \circ h^{-1} \circ \iota_2 : Y_2 \to X_2$. Since $\pi_2 \circ h = g \circ \pi_2$ and $h \circ \iota_2 = \iota_2 \circ g$, $g \circ k = \pi_2 \circ h \circ h^{-1} \circ \iota_2 = 1$ and $k \circ g = \pi_2 \circ h^{-1} \circ h \circ \iota_2 = 1$. $\square$

The map $g$ is the *Schur complement* of $f_{11}$. The second claim is a cancellation rule.

::: mathlib

`CategoryTheory.Biprod.gaussian` · `Mathlib.CategoryTheory.Preadditive.Biproducts`

The data `L`, `R`, `g₂₂` with `L.hom ≫ f ≫ R.hom = biprod.map (biprod.inl ≫ f ≫ biprod.fst) g₂₂`. The matrices are `Biprod.unipotentLower` and `Biprod.unipotentUpper`. The cancellation rule is `Biprod.isoElim`. The file also proves `Biprod.column_nonzero_of_iso`: a column of an isomorphism is not zero unless its source is a zero object.

<?decl CategoryTheory.Biprod.gaussian?>
:::

Now drop the group structure. Let $C$ have zero morphisms and binary biproducts. For $f, g : X \to Y$ there are two candidate sums. The *left sum* is $f +_l g = \nabla_Y \circ \langle f, g \rangle$ and the *right sum* is $f +_r g = [f, g] \circ \Delta_X$, where $\Delta_X = \langle 1, 1 \rangle : X \to X \oplus X$ and $\nabla_Y = [1, 1] : Y \oplus Y \to Y$.

**Theorem (Semiadditive structure).** The two sums are equal, and with $0$ they make each $\mathrm{Hom}(X, Y)$ a commutative monoid. Composition is bilinear for this addition. If $C$ is preadditive, this addition is the given one, so a category with binary biproducts has at most one preadditive structure.

*Proof.* First, $0$ is a unit for both sums. The map $\langle f, 0 \rangle$ equals $\iota_1 \circ f$, because both have components $f$ and $0$. So $f +_l 0 = \nabla \circ \iota_1 \circ f = f$. The other three unit laws are the same. Second, the interchange law holds: $(f +_r g) +_l (h +_r k) = (f +_l h) +_r (g +_l k)$. To see this, let $D = \langle [f, g], [h, k] \rangle : X \oplus X \to Y \oplus Y$. Then $D \circ \Delta = \langle f +_r g, h +_r k \rangle$, so $\nabla \circ D \circ \Delta$ is the left side. Also $D \circ \iota_1 = \langle f, h \rangle$ and $D \circ \iota_2 = \langle g, k \rangle$, so $\nabla \circ D = [f +_l h, g +_l k]$ and $\nabla \circ D \circ \Delta$ is the right side.

Now apply the Eckmann-Hilton argument. Write $\star$ for $+_l$ and $\bullet$ for $+_r$, with common unit $0$ and interchange $(a \bullet b) \star (c \bullet d) = (a \star c) \bullet (b \star d)$. Then $a \star b = (a \bullet 0) \star (0 \bullet b) = (a \star 0) \bullet (0 \star b) = a \bullet b$. Also $a \star b = (0 \bullet a) \star (b \bullet 0) = (0 \star b) \bullet (a \star 0) = b \bullet a$. So the sums agree and are commutative. For associativity, $(a \bullet b) \bullet c = (a \bullet b) \star (0 \bullet c) = (a \star 0) \bullet (b \star c) = a \bullet (b \bullet c)$.

Bilinearity: $u \circ (f +_l g) = u \circ \nabla \circ \langle f, g \rangle = \nabla \circ (u \oplus u) \circ \langle f, g \rangle = \nabla \circ \langle uf, ug \rangle = uf +_l ug$. The other side uses $+_r$ in the same way. Last, if $C$ is preadditive, $\nabla = \pi_1 + \pi_2$, because both maps have the same composites with $\iota_1$ and $\iota_2$. Then $\nabla \circ \langle f, g \rangle = \pi_1 \langle f, g \rangle + \pi_2 \langle f, g \rangle = f + g$. $\square$

**Theorem (Additive functors and biproducts).** Let $F : C \to D$ be a functor between preadditive categories. If $F$ is additive, it preserves finite biproducts. If $C$ has binary biproducts and $F$ preserves zero morphisms and binary biproducts, then $F$ is additive.

*Proof.* Let $F$ be additive and let $(P, \pi, \iota)$ be a biproduct. Then $F\pi_k \circ F\iota_j = F(\delta_{jk}) = \delta_{jk}$, since $F(0) = 0$. Also $\sum_j F\iota_j \circ F\pi_j = F(\sum_j \iota_j \pi_j) = F(1) = 1$. By the total identity theorem, the image bicone is a bilimit. For the converse, $f + g = [f, g] \circ \Delta_X$ by the semiadditive theorem. Let $c : F(X \oplus X) \to FX \oplus FX$ be the comparison map with components $F\pi_1, F\pi_2$. It is an isomorphism by hypothesis. Its components give $c \circ F\Delta_X = \Delta_{FX}$, and the components of $c \circ F\iota_j$ show $c \circ F\iota_j = \iota_j$, so $F[f, g] = [Ff, Fg] \circ c$. Hence $F(f + g) = [Ff, Fg] \circ c \circ F\Delta_X = [Ff, Fg] \circ \Delta_{FX} = Ff + Fg$. $\square$

### Examples

**Example (Matrices over a ring).** Let $R$ be a ring. In `Mat R` the objects are finite types and a morphism $m \to n$ is an $m \times n$ matrix over $R$. The biproduct is the disjoint union, and the matrix calculus above is ordinary matrix multiplication. Mathlib proves `Mat R ≌ Mat_ (SingleObj Rᵐᵒᵖ)`. The opposite ring appears because `f ≫ g` lists the factors in the reverse order of a product in $R$.

**Example (Cancellation for modules).** Let $X_1$ be an $R$-module and let $\theta : X_1 \oplus X_2 \to X_1 \oplus Y_2$ be an isomorphism whose corner $X_1 \to X_1$ is $1$. Gaussian elimination gives $X_2 \cong Y_2$. The hypothesis on the corner is necessary: for $R = \mathbb{Z}$ there is an isomorphism $\mathbb{Z}^{\mathbb{N}} \oplus \mathbb{Z} \cong \mathbb{Z}^{\mathbb{N}} \oplus 0$, but $\mathbb{Z} \not\cong 0$.

**Counterexample (A functor that is not additive).** Let $F : \mathrm{Ab} \to \mathrm{Ab}$ send $A$ to $A \otimes A$ and $f$ to $f \otimes f$. Then $F(0) = 0$, but $F(2 \cdot 1_{\mathbb{Z}})$ is multiplication by $4$ on $\mathbb{Z} \otimes \mathbb{Z} \cong \mathbb{Z}$, while $F(1) + F(1)$ is multiplication by $2$.

### The library around it

::: mathlib

`CategoryTheory.Mat_` · `Mathlib.CategoryTheory.Preadditive.Mat`

An object of `Mat_ C` is a finite type `ι` and a family `X : ι → C`. A morphism is a matrix of morphisms of `C`, and composition is the sum in the multiplication rule. `Mat_ C` is preadditive and has finite biproducts. The functor `Mat_.embedding C` is full, faithful and additive, and `Mat_.isoBiproductEmbedding` writes each object as a biproduct of embedded objects. For an additive `F : C ⥤ D` into a category with finite biproducts, `Mat_.lift F` sends `X` to `⨁ fun i => F.obj (X.X i)`. `Mat_.embeddingLiftIso` and `Mat_.liftUnique` give the universal property. If `C` already has finite biproducts, `Mat_.equivalenceSelfOfHasFiniteBiproducts` gives `Mat_ C ≌ C`.

<?decl CategoryTheory.Mat_?>
:::

::: mathlib

`CategoryTheory.SemiadditiveOfBinaryBiproducts.addCommMonoidHomOfHasBinaryBiproducts` · `Mathlib.CategoryTheory.Preadditive.OfBiproducts`

The commutative monoid on `X ⟶ Y`, built from `leftAdd`, `rightAdd` and the interchange law `distrib` by `EckmannHilton`. The theorem `add_eq_left_addition` gives the second formula for the sum. The uniqueness of a preadditive structure is the instance `subsingleton_preadditive_of_hasBinaryBiproducts` in the file of biproducts.

<?decl CategoryTheory.SemiadditiveOfBinaryBiproducts.addCommMonoidHomOfHasBinaryBiproducts?>
:::

The file `Preadditive.HomOrthogonal` treats a family $s : \iota \to C$ that is *hom orthogonal*, `HomOrthogonal`: for $i \neq j$ there is at most one morphism $s_i \to s_j$, and it is $0$ when $C$ has zero morphisms. A morphism between biproducts $\bigoplus_a s_{f(a)} \to \bigoplus_b s_{g(b)}$ then has only diagonal blocks. The equivalence `HomOrthogonal.matrixDecomposition` turns it into a family of matrices, one for each $i \in \iota$, with entries in $\operatorname{End}(s_i)$. The lemma `HomOrthogonal.matrixDecomposition_id` sends the identity to the identity matrices, and `HomOrthogonal.matrixDecomposition_comp` sends a composite to the product of the matrices in the reverse order. `HomOrthogonal.matrixDecompositionAddEquiv` and `HomOrthogonal.matrixDecompositionLinearEquiv` are the additive and the linear forms. If each ring $\operatorname{End}(s_i)$ has invariant basis number, for example when each $s_i$ is simple, the theorem `HomOrthogonal.equiv_of_iso` says that two isomorphic biproducts have the same multiplicities. The proof is short: an isomorphism and its inverse give, for each $i$, two matrices whose products are identity matrices, so the two index sets over $i$ have the same size.

Common errors of a learner:

- The entry `fᵢⱼ` of `Biprod.ofComponents` goes from `Xᵢ` to `Yⱼ`. The usual matrix convention puts the target index first. Check the order before a calculation.
- `Mat_.lift` needs `Functor.Additive F` and finite biproducts in the target. A functor into a category without biproducts has no extension.

### Exercises

1. (A) In a preadditive category with a biproduct $X \oplus Y$, prove that $\iota_1 \circ \pi_1 + \iota_2 \circ \pi_2 = 1$ from the universal property only. *Hint:* compose with $\pi_1$ and $\pi_2$.
2. (A) Show that the automorphism of $X \oplus X$ with entries $1, 1, 0, 1$ has inverse with entries $1, -1, 0, 1$. Write both with the source-first convention.
3. (B) Let $C$ have zero morphisms and binary biproducts. Suppose that each $X$ has a map $\sigma_X : X \to X$ with $1_X + \sigma_X = 0$ for the semiadditive sum. Prove that $f \circ \sigma_X$ is an inverse of $f : X \to Y$, so $C$ is preadditive.
4. (B) Prove that an equivalence between preadditive categories is an additive functor. *Hint:* an equivalence preserves biproducts.
5. (B) Let $R$ be a field. Use `Biprod.column_nonzero_of_iso` to show that each column of an invertible matrix over $R$ has a nonzero entry. Then prove it directly from linear algebra.
6. (C) Let $C$ be preadditive. Show that the functor `Mat_.embedding C` is an equivalence if and only if $C$ has finite biproducts. *Hint:* for essential surjectivity, use `Mat_.isoBiproductEmbedding`.

### Notes and history

The matrix calculus for direct sums is as old as linear algebra. The axioms of an additive category, with biproducts in place of direct sums, are in the work of Mac Lane on duality for groups from 1950 and in Grothendieck's paper on homological algebra of 1957. The Eckmann-Hilton argument is from the papers of Beno Eckmann and Peter Hilton of the early 1960s. The category `Mat_ C` is the additive envelope of $C$.

The Mathlib files are by Kim Morrison (biproducts in preadditive categories and `Mat_`), Markus Himmel (the semiadditive structure from binary biproducts), and Adam Topaz and Kim Morrison (additive functors).

### Reference

<?reference?>
