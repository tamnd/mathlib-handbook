---
title: Graded objects, bicomplexes and total complexes
kind: theory
modules:
  - Mathlib.CategoryTheory.GradedObject
  - Mathlib.CategoryTheory.DifferentialObject
  - Mathlib.Algebra.Homology.DifferentialObject
  - Mathlib.Algebra.Homology.HomologicalBicomplex
  - Mathlib.Algebra.Homology.TotalComplex
  - Mathlib.Algebra.Homology.ComplexShapeSigns
  - Mathlib.Algebra.Homology.Embedding.Basic
  - Mathlib.Algebra.Homology.Embedding.TruncGE
explains:
  E3: [CategoryTheory.GradedObject, CategoryTheory.GradedObject.mapObj, CategoryTheory.DifferentialObject, HomologicalComplex.dgoEquivHomologicalComplex, HomologicalComplex₂, TotalComplexShape, HomologicalComplex₂.total, HomologicalComplex₂.D₂_D₁, ComplexShape.Embedding, HomologicalComplex.truncGE, HomologicalComplex.πTruncGE]
  E2: [CategoryTheory.GradedObjectWithShift, CategoryTheory.GradedObject.categoryOfGradedObjects, CategoryTheory.GradedObject.eval, CategoryTheory.GradedObject.isoMk, CategoryTheory.GradedObject.comap, CategoryTheory.GradedObject.hasShift, CategoryTheory.GradedObject.total, CategoryTheory.GradedObject.HasMap, CategoryTheory.GradedObject.ιMapObj, CategoryTheory.GradedObject.descMapObj, CategoryTheory.GradedObject.mapMap, CategoryTheory.DifferentialObject.d, CategoryTheory.DifferentialObject.d_squared, CategoryTheory.DifferentialObject.Hom, HomologicalComplex₂.toGradedObject, HomologicalComplex₂.flip, HomologicalComplex₂.flipEquivalence, HomologicalComplex₂.d_comm, ComplexShape.π, ComplexShape.ε₁, ComplexShape.ε₂, ComplexShape.ε₂_ε₁, ComplexShape.TensorSigns, ComplexShape.ε, ComplexShape.ε_up_ℤ, ComplexShape.ε_down_ℕ, TotalComplexShapeSymmetry, HomologicalComplex₂.HasTotal, HomologicalComplex₂.ιTotal, HomologicalComplex₂.totalDesc, HomologicalComplex₂.D₁, HomologicalComplex₂.D₂, HomologicalComplex₂.D₁_D₁, HomologicalComplex₂.D₂_D₂, HomologicalComplex₂.totalFunctor, ComplexShape.Embedding.IsTruncGE, ComplexShape.Embedding.IsRelIff, ComplexShape.embeddingUpIntGE, ComplexShape.embeddingUpNat, HomologicalComplex.truncGE', HomologicalComplex.isIso_πTruncGE_iff, ComplexShape.Embedding.truncGEFunctor]
  E1: auto
families: []
requires: [V24.C04, V25.C02, V25.C05, V26.C02, V26.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Graded objects, bicomplexes and total complexes

### Overview

Many complexes in algebra have two indices. The tensor product of two complexes $A$ and $B$ has the terms $A^p \otimes B^q$. A resolution of each term of a complex gives a grid of objects. The Hom of two complexes and the Čech complex of a sheaf complex are other cases. Such a grid, with a horizontal and a vertical differential, is a *bicomplex*, and it has a *total complex* with the terms $\bigoplus_{p+q=n} K^{p,q}$. The construction needs a sign, so that the total differential squares to zero.

This section builds the objects in the order of Mathlib. A graded object is a family of objects indexed by a type. A differential object is an object with a map to its shift that squares to zero, and complexes are a special case. A bicomplex is a complex of complexes. Its total complex is defined for each choice of index map and signs that satisfies one equation. The section proves that the total differential squares to zero, that a first quadrant bicomplex with exact columns has an acyclic total complex, and that the canonical truncation $\tau^{\geq p}$ keeps the cohomology in degrees $\geq p$. The next section uses these complexes to construct spectral sequences.

The complexes are cochain complexes unless the text says otherwise. Mathlib writes `f ≫ g` for the composite $g \circ f$.

### Definitions

**Definition (Graded object).** Let $\beta$ be a type and $C$ a category. A *$\beta$-graded object* of $C$ is a family $X = (X_b)_{b \in \beta}$ of objects of $C$. A morphism $f : X \to Y$ is a family of morphisms $f_b : X_b \to Y_b$. The graded objects form the category $C^\beta$.

For a map $p : \beta \to \gamma$, the *push forward* $p_* X$ is the $\gamma$-graded object with
$$(p_* X)_c = \coprod_{b \in p^{-1}(c)} X_b,$$
when these coproducts exist. Each $X_b$ comes with the inclusion $\iota_b : X_b \to (p_* X)_{p(b)}$.

**Definition (Shift of a graded object).** Let $\beta$ be an additive group and $s \in \beta$. The shift of $X \in C^\beta$ by $n \in \mathbb{Z}$ is $(X[n])_t = X_{t + ns}$.

**Definition (Differential object).** Let $C$ be a category with zero morphisms and a shift by $\mathbb{Z}$. A *differential object* is an object $X$ with a morphism $d : X \to X[1]$ such that $d[1] \circ d = 0$. A morphism of differential objects is a morphism $f : X \to Y$ with $d_Y \circ f = f[1] \circ d_X$.

**Definition (Bicomplex).** A *bicomplex* $K$ in a preadditive category is a family of objects $K^{p,q}$ for $(p, q) \in \mathbb{Z}^2$, with horizontal maps $d_h : K^{p,q} \to K^{p+1,q}$ and vertical maps $d_v : K^{p,q} \to K^{p,q+1}$, such that
$$d_h d_h = 0, \qquad d_v d_v = 0, \qquad d_h d_v = d_v d_h.$$
Equivalently, $K$ is a complex of complexes: each column $K^{p,\bullet}$ is a complex with differential $d_v$, and $d_h : K^{p,\bullet} \to K^{p+1,\bullet}$ is a map of complexes.

A bicomplex can have other index types, for example $\mathbb{N}^2$ with homological differentials. The definition above is the case of two shapes $c_1 = c_2 = \operatorname{up} \mathbb{Z}$. The *flip* of $K$ exchanges the two indices.

**Definition (Total complex shape).** Let $c_1, c_2, c_{12}$ be complex shapes on index types $I_1, I_2, I_{12}$. A *total complex shape* is a map $\pi : I_1 \times I_2 \to I_{12}$ with signs $\varepsilon_1, \varepsilon_2 : I_1 \times I_2 \to \{\pm 1\}$, such that $\pi$ sends the relations of $c_1$ in the first variable and of $c_2$ in the second variable to relations of $c_{12}$, and such that
$$\varepsilon_2(i_1, i_2)\, \varepsilon_1(i_1, i_2') = -\varepsilon_1(i_1, i_2)\, \varepsilon_2(i_1', i_2) \qquad \text{whenever } c_1.\mathrm{Rel}(i_1, i_1'),\ c_2.\mathrm{Rel}(i_2, i_2').$$

For $\mathbb{Z}$ with the shape $\operatorname{up}$, the standard choice is $\pi(p, q) = p + q$, $\varepsilon_1(p, q) = 1$ and $\varepsilon_2(p, q) = (-1)^p$. The condition reads $(-1)^p \cdot 1 = -1 \cdot (-1)^{p+1}$, which holds.

**Definition (Total complex).** Let $K$ be a bicomplex with a total complex shape such that the push forward of $(K^{i_1, i_2})$ along $\pi$ exists. The *total complex* $\operatorname{Tot}(K)$ has the terms $\operatorname{Tot}(K)^n = \coprod_{\pi(i_1, i_2) = n} K^{i_1, i_2}$ and the differential $D = D_1 + D_2$, where on the summand $K^{i_1,i_2}$
$$D_1 = \varepsilon_1(i_1, i_2)\, d_h, \qquad D_2 = \varepsilon_2(i_1, i_2)\, d_v,$$
followed by the inclusion of the target summand.

For the standard shape on $\mathbb{Z}$, $D(x) = d_h x + (-1)^p d_v x$ for $x \in K^{p,q}$.

**Definition (Embedding of complex shapes).** An *embedding* $e : c \to c'$ of complex shapes on $I$ and $I'$ is an injective map $e : I \to I'$ that sends relations of $c$ to relations of $c'$. It is of type *truncation from below* if, whenever $c'.\mathrm{Rel}(e(i), j)$, the index $j$ is in the image of $e$.

The map $n \mapsto p + n$ from $\mathbb{N}$ to $\mathbb{Z}$ with the shapes $\operatorname{up}$ is such an embedding: the successor of $p + n$ is $p + n + 1$, which is in the image.

**Definition (Canonical truncation).** Let $K$ be a cochain complex indexed by $\mathbb{Z}$ and $p \in \mathbb{Z}$. The truncation $\tau^{\geq p} K$ has the terms
$$(\tau^{\geq p} K)^n = 0 \ (n < p), \qquad (\tau^{\geq p} K)^p = \operatorname{coker}(d : K^{p-1} \to K^p), \qquad (\tau^{\geq p} K)^n = K^n \ (n > p),$$
with the differentials induced by $d$. The projection $\pi : K \to \tau^{\geq p} K$ is the identity in degrees $> p$, the quotient map in degree $p$, and zero below.

The differential $\operatorname{coker}(d^{p-1}) \to K^{p+1}$ exists because $d^p \circ d^{p-1} = 0$.

::: mathlib
`CategoryTheory.GradedObject` · `Mathlib.CategoryTheory.GradedObject`

`GradedObject β C` is the type `β → C`, and `categoryOfGradedObjects` is the product category. For `p : I → J`, the class `X.HasMap p` asserts that the coproducts of the fibers exist, `X.mapObj p : GradedObject J C` is the push forward, `X.ιMapObj p i j h` is the inclusion of `X i` when `p i = j`, and `descMapObj` is the map out of the push forward. `GradedObjectWithShift s C` with `GradedObject.hasShift s` is the shift by multiples of `s`.

<?decl CategoryTheory.GradedObject?>
:::

::: mathlib
`HomologicalComplex₂` · `Mathlib.Algebra.Homology.HomologicalBicomplex`

`HomologicalComplex₂ C c₁ c₂` is an abbreviation for `HomologicalComplex (HomologicalComplex C c₂) c₁`. For `K` in it, `(K.X i₁).X i₂` is the object $K^{i_1, i_2}$, `(K.d i₁ i₁').f i₂` is the horizontal differential and `(K.X i₁).d i₂ i₂'` is the vertical one. The commutation of the squares is `HomologicalComplex₂.d_comm`, and it holds because `K.d i₁ i₁'` is a map of complexes. `K.flip` exchanges the roles, and `flipEquivalence` is the resulting equivalence of categories.

<?decl HomologicalComplex₂?>
:::

### Theorems and proofs

**Theorem (The total differential squares to zero).** For each bicomplex with a total complex shape, $D \circ D = 0$ on $\operatorname{Tot}(K)$.

*Proof.* Expand $D D = D_1 D_1 + D_2 D_2 + (D_1 D_2 + D_2 D_1)$. On a summand $K^{i_1,i_2}$, $D_1 D_1$ is $\varepsilon_1(i_1', i_2) \varepsilon_1(i_1, i_2)\, d_h d_h = 0$, and in the same way $D_2 D_2 = 0$. For the mixed terms, let $i_1'$ and $i_2'$ be the successors of $i_1$ and $i_2$; if one of them does not exist, the corresponding differential is zero and the mixed terms vanish. The two paths from $K^{i_1,i_2}$ to $K^{i_1',i_2'}$ give
$$D_1 D_2 = \varepsilon_2(i_1, i_2)\, \varepsilon_1(i_1, i_2')\, d_h d_v, \qquad D_2 D_1 = \varepsilon_1(i_1, i_2)\, \varepsilon_2(i_1', i_2)\, d_v d_h.$$
Since $d_h d_v = d_v d_h$, their sum is $(\varepsilon_2(i_1,i_2)\varepsilon_1(i_1,i_2') + \varepsilon_1(i_1,i_2)\varepsilon_2(i_1',i_2))\, d_h d_v$. The sign condition says that the factor is zero. A map out of a coproduct is zero when it is zero on each summand, so $DD = 0$. $\square$

The proof shows why the sign is needed. Without it, $D_1 D_2 + D_2 D_1 = 2\, d_h d_v$, which is not zero in general.

**Theorem (Complexes are differential objects).** Let $\beta = \mathbb{Z}$ and $b \in \mathbb{Z}$. Differential objects in the category of $\mathbb{Z}$-graded objects with the shift by multiples of $b$ are the same as complexes of the shape $\operatorname{up}'(b)$, whose differential goes from degree $i$ to degree $i + b$. The two categories are equivalent.

*Proof.* A differential object is a family $(X_i)$ with $d : X \to X[1]$, so a family of maps $d_i : X_i \to X_{i+b}$. The condition $d[1] \circ d = 0$ in degree $i$ is $d_{i+b} \circ d_i = 0$. A complex of shape $\operatorname{up}'(b)$ is a family $X_i$ with maps $d_{i,j}$ for all $i, j$, zero unless $j = i + b$, such that consecutive maps compose to zero. Send $(X, d)$ to the complex with $d_{i,i+b} = d_i$ and $d_{i,j} = 0$ for $j \neq i + b$. A morphism of differential objects is a family $f_i$ with $d_i f_i = f_{i+b} d_i$, which is a map of complexes. The inverse functor keeps only the maps $d_{i,i+b}$. The composites are isomorphic to the identities; they are not equal, because $X[1]_i = X_{i+b}$ holds only after an identification of indices. $\square$

**Theorem (Acyclic assembly).** Let $K$ be a bicomplex with $K^{p,q} = 0$ unless $p \geq 0$ and $q \geq 0$. Suppose that each column $K^{p,\bullet}$ is exact, with $H^q(K^{p,\bullet}) = 0$ for all $q$, including $q = 0$. Then $\operatorname{Tot}(K)$ is acyclic.

*Proof.* The proof is for modules; in an abelian category it runs with generalized elements. Let $x \in \operatorname{Tot}(K)^n$ with $Dx = 0$. Write $x = (x_0, \dots, x_n)$ with $x_p \in K^{p, n-p}$. Suppose that $x_p = 0$ for $p < k$, with $0 \leq k \leq n$. The component of $Dx$ in $K^{k, n+1-k}$ is $d_h x_{k-1} + (-1)^k d_v x_k = (-1)^k d_v x_k$, so $d_v x_k = 0$. If $k = n$, then $x_n \in K^{n,0}$ and $\ker(d_v) = H^0(K^{n,\bullet}) = 0$, so $x_n = 0$ and $x = 0$. If $k < n$, exactness of the column gives $y \in K^{k, n-k-1}$ with $d_v y = (-1)^k x_k$. Then $Dy = (-1)^k d_v y + d_h y = x_k + d_h y$, so $x' = x - Dy$ has $x'_p = 0$ for $p \leq k$, and $Dx' = 0$. After at most $n + 1$ steps, $x - D(y_0 + \cdots + y_{n-1}) = 0$. So each cycle is a boundary. $\square$

By symmetry, the same holds when each row is exact. This lemma gives the balance of Tor, and it is the first case of the comparison of a bicomplex with its spectral sequences in the next section.

**Theorem (Canonical truncation).** The projection $\pi : K \to \tau^{\geq p} K$ is a map of complexes. It induces an isomorphism $H^n(K) \to H^n(\tau^{\geq p} K)$ for $n \geq p$, and $H^n(\tau^{\geq p} K) = 0$ for $n < p$.

*Proof.* Write $Q = \operatorname{coker}(d^{p-1})$ with the quotient map $q : K^p \to Q$, and $\bar d : Q \to K^{p+1}$ with $\bar d q = d^p$. The map $\pi$ commutes with the differentials: in degree $p - 1$ both composites $K^{p-1} \to Q$ are zero, since $q d^{p-1} = 0$; in degree $p$, $\bar d q = d^p$. Below degree $p$ the truncation is zero, so its cohomology is zero. For $n \geq p + 2$ the terms and maps in degrees $n - 1, n, n + 1$ are the same. In degree $p + 1$ the cycles are $\ker d^{p+1}$ for both, and the boundaries are $\operatorname{im}(\bar d) = \operatorname{im}(\bar d q) = \operatorname{im}(d^p)$, since $q$ is an epimorphism. In degree $p$, $H^p(\tau^{\geq p} K) = \ker \bar d$. The map $q$ restricts to $\ker d^p \to \ker \bar d$, which is surjective since $q$ is surjective and $\bar d q = d^p$, and its kernel is $\ker q = \operatorname{im} d^{p-1}$. So $H^p(K) = \ker d^p / \operatorname{im} d^{p-1} \cong \ker \bar d$. $\square$

In particular, if $H^n(K) = 0$ for $n < p$, then $\pi$ is a quasi-isomorphism. So in the derived category of Chapter 5, a complex with cohomology in degrees $\geq p$ is isomorphic to a complex with terms in degrees $\geq p$.

### Examples

**Example (The tensor product of two complexes).** Let $A$ be the complex $\mathbb{Z} \xrightarrow{2} \mathbb{Z}$ in degrees $-1$ and $0$. It is a free resolution of $\mathbb{Z}/2$. Let $K^{p,q} = A^p \otimes A^q$, with $d_h = d_A \otimes 1$ and $d_v = 1 \otimes d_A$. The total complex in degrees $-2, -1, 0$ is
$$\mathbb{Z} \xrightarrow{x \mapsto (2x, -2x)} \mathbb{Z}^2 \xrightarrow{(a, b) \mapsto 2a + 2b} \mathbb{Z},$$
where $\mathbb{Z}^2 = K^{0,-1} \oplus K^{-1,0}$. The first map sends $x \in K^{-1,-1}$ to $d_h x \in K^{0,-1}$ and to $(-1)^{-1} d_v x \in K^{-1,0}$. The second map sends $a \in K^{0,-1}$ to $(-1)^0 d_v a$ and $b \in K^{-1,0}$ to $d_h b$. The composite is $x \mapsto 4x - 4x = 0$. The cohomology is $H^{-2} = 0$, $H^{-1} = \{(a, -a)\}/\{(2x, -2x)\} \cong \mathbb{Z}/2$ and $H^0 = \mathbb{Z}/2$. These are $\operatorname{Tor}_1(\mathbb{Z}/2, \mathbb{Z}/2)$ and $\mathbb{Z}/2 \otimes \mathbb{Z}/2$, as in Chapter 4.

**Example (Without the sign).** In the previous example, take $D = d_h + d_v$ with no sign. The first map becomes $x \mapsto (2x, 2x)$ and the composite is $x \mapsto 8x$, which is not zero. So the sign is necessary even for this small bicomplex.

**Example (Push forward along the sum).** Let $X$ be the $\mathbb{Z}^2$-graded abelian group with $X_{p,q} = \mathbb{Z}$ for $0 \leq p, q \leq 2$ and $0$ otherwise. The push forward along $\pi(p,q) = p + q$ has ranks $1, 2, 3, 2, 1$ in degrees $0$ to $4$, the number of pairs in each fiber that lie in the square.

**Example (A truncation).** Let $K$ be $\mathbb{Z} \xrightarrow{2} \mathbb{Z}$ in degrees $0$ and $1$. Then $\tau^{\geq 1} K$ is $\mathbb{Z}/2$ in degree $1$. The cohomology of $K$ is $H^0 = 0$ and $H^1 = \mathbb{Z}/2$, and $\pi$ is a quasi-isomorphism, as the theorem predicts since $H^0(K) = 0$. For $\tau^{\geq 0} K = K$ nothing changes.

### The library around it

::: mathlib
`TotalComplexShape` · `Mathlib.Algebra.Homology.ComplexShapeSigns`

The class `TotalComplexShape c₁ c₂ c₁₂` holds `π`, `ε₁`, `ε₂` with values in `ℤˣ`, the relations `rel₁` and `rel₂`, and the condition `ε₂_ε₁`, read through `ComplexShape.π`, `ComplexShape.ε₁` and `ComplexShape.ε₂`. The class `ComplexShape.TensorSigns c` gives a sign `ComplexShape.ε c`, and then an instance `TotalComplexShape c c c` with `π = (· + ·)`, `ε₁ = 1` and `ε₂ ⟨p, q⟩ = c.ε p`. For `up ℤ` this sign is `ComplexShape.ε_up_ℤ`, the value `n.negOnePow`, and for `down ℕ` it is `ComplexShape.ε_down_ℕ`, the value $(-1)^n$. `TotalComplexShapeSymmetry` holds the signs that compare the total complexes of `K` and of `K.flip`.

<?decl TotalComplexShape?>
:::

::: mathlib
`HomologicalComplex₂.total` · `Mathlib.Algebra.Homology.TotalComplex`

`K.total c₁₂` needs `[K.HasTotal c₁₂]`, which is `K.toGradedObject.HasMap (ComplexShape.π c₁ c₂ c₁₂)`. Its terms are `K.toGradedObject.mapObj π`, and its differential is `K.D₁ c₁₂ + K.D₂ c₁₂`. The lemmas `D₁_D₁`, `D₂_D₂` and `D₂_D₁ : K.D₂ c₁₂ i₁₂ i₁₂' ≫ K.D₁ c₁₂ i₁₂' i₁₂'' = - K.D₁ c₁₂ i₁₂ i₁₂' ≫ K.D₂ c₁₂ i₁₂' i₁₂''` are the three steps of the proof above. Maps out of the total complex are built with `K.ιTotal` and `K.totalDesc`, and `totalFunctor` makes the construction functorial.

<?decl HomologicalComplex₂.total?>
:::

::: mathlib
`HomologicalComplex.truncGE` · `Mathlib.Algebra.Homology.Embedding.TruncGE`

For `e : ComplexShape.Embedding c c'` with `[e.IsTruncGE]` and `K : HomologicalComplex C c'`, `K.truncGE' e` is a complex of shape `c` and `K.truncGE e` is its extension to shape `c'`. For `e = ComplexShape.embeddingUpIntGE p`, this is $\tau^{\geq p} K$. The projection is `K.πTruncGE e`, an epimorphism, and `isIso_πTruncGE_iff` says that it is an isomorphism exactly when `K` is strictly supported in the image of `e`. The statement on cohomology, `HomologicalComplex.quasiIsoAt_πTruncGE`, is in `Mathlib.Algebra.Homology.Embedding.TruncGEHomology`.

<?decl HomologicalComplex.truncGE?>
:::

The differential objects of `Mathlib.CategoryTheory.DifferentialObject` are the structure `DifferentialObject S C` with the fields `obj`, `d` and `d_squared`, for a shift by an additive monoid `S`. The equivalence of this theorem is `HomologicalComplex.dgoEquivHomologicalComplex`, from `DifferentialObject ℤ (GradedObjectWithShift b V)` to `HomologicalComplex V (ComplexShape.up' b)`. Mathlib does not use it to define complexes. The source of `HomologicalComplex` stores a morphism for each pair of indices, which avoids the identification $X_{i+b} = X[1]_i$ in each lemma.

Common errors of a learner:

- In `HomologicalComplex₂ C c₁ c₂` the outer index is the first one. `K.X p` is a whole column, a complex of shape `c₂`.
- The sign in the total complex is on the vertical differential, $(-1)^p d_v$, for the standard shape on `up ℤ`. Other books put it on the horizontal one. The two total complexes are isomorphic, but not equal.
- `K.total` needs the instance `HasTotal`. For a bicomplex of modules it is automatic, because coproducts exist; for a general category it must be checked.
- `truncGE'` lives on the smaller shape, and `truncGE` on the original one.

### Exercises

1. (A) Check that the sign choice $\varepsilon_1(p, q) = (-1)^q$, $\varepsilon_2(p, q) = 1$ also satisfies the sign condition on $\mathbb{Z}^2$. *Hint:* substitute in the equation of the definition.
2. (A) Compute the total complex of the bicomplex with $K^{0,0} = K^{1,0} = K^{0,1} = K^{1,1} = \mathbb{Z}$, all differentials the identity, and $0$ elsewhere. Show that it is acyclic. *Hint:* the total complex is $\mathbb{Z} \to \mathbb{Z}^2 \to \mathbb{Z}$.
3. (B) Let $A$ be $\mathbb{Z} \xrightarrow{m} \mathbb{Z}$ and $B$ be $\mathbb{Z} \xrightarrow{n} \mathbb{Z}$, both in degrees $-1, 0$. Compute the cohomology of $\operatorname{Tot}(A^p \otimes B^q)$. *Hint:* the answer is $\mathbb{Z}/\gcd(m, n)$ in degrees $-1$ and $0$.
4. (B) Show that the total complex of $K$ and of its flip are isomorphic, with the isomorphism $(-1)^{pq}$ on $K^{p,q}$. *Hint:* compare the two differentials on each summand.
5. (B) Define the dual truncation $\tau^{\leq p} K$ with $\ker(d^p)$ in degree $p$, and prove that the inclusion $\tau^{\leq p} K \to K$ induces isomorphisms on $H^n$ for $n \leq p$. *Hint:* dualize the proof of the truncation theorem.
6. (C) Prove the acyclic assembly theorem for a bicomplex with $K^{p,q} = 0$ unless $p \geq 0$ and $q \leq 0$, with exact rows. Find a bicomplex with exact rows and nonzero total cohomology when both $p$ and $q$ range over all of $\mathbb{Z}$. *Hint:* for the second part, use infinitely many nonzero terms on each antidiagonal and products in place of sums.

### Notes and history

Double complexes and their total complexes are in Cartan and Eilenberg, *Homological Algebra* (1956), where they give the balance of the derived functors of the tensor product. The canonical truncations are standard in the theory of the derived category of Verdier.

The Mathlib Authors of `CategoryTheory.GradedObject` are Kim Morrison and Joël Riou. `CategoryTheory.DifferentialObject` and `Homology.DifferentialObject` are by Kim Morrison. `HomologicalBicomplex` is by Kim Morrison and Joël Riou. `ComplexShapeSigns`, `TotalComplex`, `Embedding.Basic` and `Embedding.TruncGE` are by Joël Riou.

### Reference

<?reference?>
