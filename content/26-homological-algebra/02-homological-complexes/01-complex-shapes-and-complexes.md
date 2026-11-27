---
title: Complex shapes and complexes
kind: theory
modules:
  - Mathlib.Algebra.Homology.ComplexShape
  - Mathlib.Algebra.Homology.HomologicalComplex
  - Mathlib.Algebra.Homology.Single
  - Mathlib.Algebra.Homology.Additive
  - Mathlib.Algebra.Homology.Augment
  - Mathlib.Algebra.Homology.Opposite
explains:
  E3: [ComplexShape, ComplexShape.up, ComplexShape.down, HomologicalComplex, HomologicalComplex.Hom, ChainComplex, CochainComplex, HomologicalComplex.single, ChainComplex.toSingle₀Equiv, CategoryTheory.Functor.mapHomologicalComplex, ChainComplex.augment, HomologicalComplex.op]
  E2: [ComplexShape.up', ComplexShape.down', ComplexShape.symm, ComplexShape.next, ComplexShape.prev, ComplexShape.next_eq', HomologicalComplex.shape, HomologicalComplex.d_comp_d, HomologicalComplex.Hom.comm, HomologicalComplex.hom_ext, ChainComplex.of, CochainComplex.of, ChainComplex.mk, HomologicalComplex.eval, HomologicalComplex.XIsoOfEq, HomologicalComplex.Hom.isoOfComponents, HomologicalComplex.xNext, HomologicalComplex.singleObjXSelf, ChainComplex.single₀, CochainComplex.single₀, ChainComplex.fromSingle₀Equiv, HomologicalComplex.instFullSingle, HomologicalComplex.instPreadditive, CategoryTheory.NatTrans.mapHomologicalComplex, CategoryTheory.Equivalence.mapHomologicalComplex, HomologicalComplex.singleMapHomologicalComplex, ChainComplex.truncate, ChainComplex.truncateAugment, ChainComplex.augmentTruncate, CochainComplex.augment, HomologicalComplex.unop, HomologicalComplex.opEquivalence]
  E1: auto
families: []
requires: [V07, V24.C02, V24.C08, V25.C01, V26.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Complex shapes and complexes

### Overview

A chain complex of abelian groups is a sequence $\cdots \to X_2 \xrightarrow{d_2} X_1 \xrightarrow{d_1} X_0$ with $d_{n} \circ d_{n+1} = 0$. A cochain complex goes the other way, $X^0 \to X^1 \to X^2 \to \cdots$, and is often indexed by all of $\mathbb{Z}$. Other indexings occur too: a $2$-periodic complex, a complex graded by $\mathbb{Z}^2$ along one direction, a complex with the differential of degree $-2$. Mathlib treats all of them at once. A *complex shape* on an index type $\iota$ says which pairs $(i, j)$ carry a differential $X_i \to X_j$. A complex of that shape has an object $X_i$ for each $i$ and a morphism $d_{ij}$ for *every* pair, which is zero unless the shape allows it.

The point of this choice is to avoid equations between objects. In a chain complex indexed by $\mathbb{N}$ the differential at $n+1$ goes to $X_n$. If a proof produces an index $m$ with $m = n + 1$ only as a proposition, then $X_m$ and $X_{n+1}$ are not the same term, and a morphism into one is not a morphism into the other. With a differential $d_{ij}$ for all $i, j$, the proof can use $d_{m n}$ and the hypothesis that $m$ is the successor of $n$.

This section defines shapes and complexes, the single complex, the action of a functor on complexes, augmentation and the opposite complex. Section 2 defines homology. It uses Chapter 1 for short complexes, Volume 24, Chapters 2 and 8, for functors and zero morphisms, and Volume 25, Chapter 1, for preadditive categories.

### Definitions

**Definition (Complex shape).** A *complex shape* on a type $\iota$ is a relation $R$ on $\iota$ such that each $i$ has at most one $j$ with $R(i, j)$, and each $j$ has at most one $i$ with $R(i, j)$. Read $R(i, j)$ as "a differential goes from $i$ to $j$".

For a shape $c$, the *next* index $c.\mathrm{next}(i)$ is the unique $j$ with $R(i, j)$ if it exists, and $i$ otherwise. The *previous* index $c.\mathrm{prev}(j)$ is defined dually. The *symmetric* shape $c.\mathrm{symm}$ has the relation $R(j, i)$.

**Definition (Up and down).** Let $\alpha$ be an additive monoid in which addition on the right cancels, and $a \in \alpha$. The shape $\mathrm{up}'(a)$ has $R(i, j)$ if and only if $i + a = j$. The shape $\mathrm{down}'(a)$ has $R(i, j)$ if and only if $j + a = i$. The shapes $\mathrm{up} = \mathrm{up}'(1)$ and $\mathrm{down} = \mathrm{down}'(1)$ are the usual ones.

Right cancellation gives the two uniqueness conditions: if $i + a = j$ and $i' + a = j$, then $i = i'$, and $j$ is determined by $i$ because addition is a function.

**Definition (Homological complex).** Let $C$ be a category with zero morphisms and $c$ a complex shape on $\iota$. A *homological complex* $K$ of shape $c$ consists of objects $X_i$ for $i \in \iota$ and morphisms $d_{ij} : X_i \to X_j$ for all $i, j$, such that:

1. $d_{ij} = 0$ if $R(i, j)$ does not hold;
2. $d_{jk} \circ d_{ij} = 0$ whenever $R(i, j)$ and $R(j, k)$.

A *morphism* $\varphi : K \to L$ is a family of morphisms $\varphi_i : X_i \to Y_i$ with $\varphi_j \circ d^K_{ij} = d^L_{ij} \circ \varphi_i$ whenever $R(i, j)$.

**Definition (Chain and cochain complexes).** A *chain complex* indexed by $\alpha$ is a homological complex of shape $\mathrm{down}$, so its differentials go from $n+1$ to $n$. A *cochain complex* is a homological complex of shape $\mathrm{up}$, so its differentials go from $n$ to $n+1$. The usual choices are $\alpha = \mathbb{N}$ for chain complexes and $\alpha = \mathbb{Z}$ for cochain complexes.

**Definition (Single complex).** Let $C$ have a zero object, and $j \in \iota$. The *single complex* on an object $A$ in degree $j$ has $X_j = A$, $X_i = 0$ for $i \ne j$, and all differentials zero. For $\iota = \mathbb{N}$ and $j = 0$ it is written $A[0]$ here.

**Definition (Augmentation and truncation).** Let $K$ be a chain complex indexed by $\mathbb{N}$. Its *truncation* is the chain complex with objects $X_{n+1}$ in degree $n$ and the same differentials. If $\varepsilon : X_0 \to A$ satisfies $\varepsilon \circ d_{10} = 0$, the *augmentation* of $K$ by $\varepsilon$ is the chain complex
$$\cdots \to X_1 \xrightarrow{d_{10}} X_0 \xrightarrow{\varepsilon} A,$$
with $A$ in degree $0$ and $X_n$ in degree $n + 1$.

**Definition (Opposite complex).** The *opposite* of a complex $K$ of shape $c$ in $C$ is the complex $K^{\mathrm{op}}$ of shape $c.\mathrm{symm}$ in $C^{\mathrm{op}}$ with objects $X_i$ and differentials $(d_{ji})^{\mathrm{op}} : X_i \to X_j$ in $C^{\mathrm{op}}$.

### Theorems and proofs

**Proposition (The complexes form a category).** The homological complexes of shape $c$ in $C$, with their morphisms, form a category with zero morphisms. If $C$ is preadditive, the category of complexes is preadditive, with $(\varphi + \psi)_i = \varphi_i + \psi_i$. A morphism $\varphi$ is an isomorphism if and only if each $\varphi_i$ is an isomorphism.

*Proof.* Composition is componentwise, and a composite of commuting squares commutes. The zero morphism has all components zero. In the preadditive case, $(\varphi_j + \psi_j) \circ d_{ij} = d_{ij} \circ \varphi_i + d_{ij} \circ \psi_i = d_{ij} \circ (\varphi_i + \psi_i)$ by bilinearity of composition, and the axioms of a preadditive category hold componentwise. If each $\varphi_i$ has an inverse $\psi_i$, then $\psi_j \circ d^L_{ij} = \psi_j \circ d^L_{ij} \circ \varphi_i \circ \psi_i = \psi_j \circ \varphi_j \circ d^K_{ij} \circ \psi_i = d^K_{ij} \circ \psi_i$, so $\psi$ is a morphism of complexes. $\square$

**Proposition (All composites of differentials vanish).** For all $i, j, k$, $d_{jk} \circ d_{ij} = 0$. For all $i, j$ and a morphism $\varphi$, $\varphi_j \circ d^K_{ij} = d^L_{ij} \circ \varphi_i$.

*Proof.* If $R(i, j)$ and $R(j, k)$ both hold, this is axiom 2. Otherwise one of $d_{ij}$, $d_{jk}$ is zero by axiom 1, and a composite with a zero morphism is zero. For the second claim, if $R(i, j)$ fails then both sides are zero. $\square$

**Proposition (Building a chain complex).** Let $X_n$ for $n \in \mathbb{N}$ be objects and $d_n : X_{n+1} \to X_n$ morphisms with $d_n \circ d_{n+1} = 0$. There is a chain complex $K$ with objects $X_n$ and $d^K_{n+1, n} = d_n$.

*Proof.* Put $d^K_{ij} = d_j \circ e$ when $i = j + 1$, where $e : X_i \to X_{j+1}$ is the identity morphism transported along the equation $i = j + 1$; and put $d^K_{ij} = 0$ otherwise. Axiom 1 holds by construction. For axiom 2, $R(i, j)$ and $R(j, k)$ mean $i = j + 1$ and $j = k + 1$, and then $d^K_{jk} \circ d^K_{ij} = d_k \circ d_{k+1} = 0$. $\square$

**Theorem (Maps to a single complex).** Let $K$ be a chain complex indexed by $\mathbb{N}$ and $A$ an object. Morphisms of complexes $K \to A[0]$ correspond bijectively to morphisms $\varepsilon : X_0 \to A$ with $\varepsilon \circ d_{10} = 0$, by $\varphi \mapsto \varphi_0$. Dually, morphisms $A[0] \to K$ correspond to morphisms $\eta : A \to X_0$, with no condition.

*Proof.* A morphism $\varphi : K \to A[0]$ has $\varphi_n : X_n \to 0$ for $n \ge 1$, and there is only one such morphism. The only nontrivial square is the one for $R(1, 0)$: $\varphi_0 \circ d_{10} = 0 \circ \varphi_1 = 0$. So $\varphi_0$ satisfies the condition. Conversely, an $\varepsilon$ with $\varepsilon \circ d_{10} = 0$, completed by zero maps, satisfies all squares: the squares for $R(n+1, n)$ with $n \ge 1$ have target $0$. The two maps are inverse because the components $\varphi_n$ for $n \ge 1$ are determined. For maps $A[0] \to K$, the square for $R(1, 0)$ reads $\eta \circ 0 = d_{10} \circ 0$, which always holds, and the other squares have source $0$. $\square$

A consequence: the functor $A \mapsto A[j]$ from $C$ to complexes is fully faithful, since a morphism $A[j] \to B[j]$ is a morphism $A \to B$ in degree $j$ with no condition.

**Theorem (Augmentation and truncation are inverse).** Let $K$ be a chain complex indexed by $\mathbb{N}$ and $\varepsilon : X_0 \to A$ with $\varepsilon \circ d_{10} = 0$. The truncation of the augmentation of $K$ by $\varepsilon$ is isomorphic to $K$. Conversely, a chain complex $L$ is isomorphic to the augmentation of its truncation by $d^L_{10}$.

*Proof.* The augmented complex has objects $X_n$ in degree $n+1$ and $A$ in degree $0$, and its differential from degree $n + 2$ to degree $n + 1$ is $d_{n+1, n}$. Truncation removes degree $0$ and shifts down by one, so it returns the objects $X_n$ in degree $n$ and the differentials $d_{n+1, n}$. The isomorphism is the identity in each degree. For $L$, the truncation has $L_{n+1}$ in degree $n$, and augmentation by $d^L_{10} : L_1 \to L_0$ adds $L_0$ in degree $0$. The condition $d^L_{10} \circ d^L_{21} = 0$ holds. The result has the objects and the differentials of $L$. $\square$

Augmentation is how a resolution enters: a projective resolution $P_\bullet \to M$ of a module $M$ is a chain complex $P$ with an augmentation $\varepsilon : P_0 \to M$ such that the augmented complex is exact. Chapter 4 uses this.

**Theorem (Functors on complexes).** Let $F : C \to D$ preserve zero morphisms. Then $F$ applied in each degree gives a functor $F_* : \mathrm{Ch}_c(C) \to \mathrm{Ch}_c(D)$. A natural transformation $\alpha : F \to G$ gives $\alpha_* : F_* \to G_*$, and an equivalence $C \simeq D$ gives an equivalence of the categories of complexes. If $C$ and $D$ have zero objects, then $F_*(A[j]) \cong (FA)[j]$.

*Proof.* The complex $F_*(K)$ has objects $F(X_i)$ and differentials $F(d_{ij})$. Axiom 1 holds because $F(0) = 0$, and axiom 2 because $F(d_{jk}) \circ F(d_{ij}) = F(d_{jk} \circ d_{ij}) = F(0) = 0$. A morphism $\varphi$ goes to $(F\varphi_i)_i$, and the squares commute because $F$ preserves composition. The components of $\alpha_*$ at $K$ are $\alpha_{X_i}$, and naturality of $\alpha$ gives the squares. For an equivalence with unit and counit isomorphisms, apply this to the functors and to the unit and counit. For the single complex, $F(0)$ is a zero object, because $F$ preserves zero morphisms and an object is zero if and only if its identity is zero. $\square$

The functor $F$ need not be additive for this theorem. For the homology of $F_*(K)$ in Section 2, the functor must also preserve the homology of short complexes, which holds for exact functors.

**Proposition (Opposite complexes).** The construction $K \mapsto K^{\mathrm{op}}$ gives an equivalence between the opposite of the category of complexes of shape $c$ in $C$ and the category of complexes of shape $c.\mathrm{symm}$ in $C^{\mathrm{op}}$.

*Proof.* Axiom 1 for $K^{\mathrm{op}}$: if $R(i, j)$ fails in $c.\mathrm{symm}$, then $R(j, i)$ fails in $c$, so $d_{ji} = 0$ and its opposite is zero. Axiom 2: in $K^{\mathrm{op}}$ the differentials from $i$ to $j$ and from $j$ to $k$ are $(d_{ji})^{\mathrm{op}}$ and $(d_{kj})^{\mathrm{op}}$, and their composite in $C^{\mathrm{op}}$ is $(d_{ji} \circ d_{kj})^{\mathrm{op}} = 0$. A morphism $\varphi : K \to L$ gives $\varphi^{\mathrm{op}} : L^{\mathrm{op}} \to K^{\mathrm{op}}$ componentwise. The inverse construction applies $(-)^{\mathrm{unop}}$ in each degree, and the two composites are the identity in each degree. $\square$

In particular the opposite of a chain complex is a cochain complex in $C^{\mathrm{op}}$. This is the duality that turns statements on projective resolutions into statements on injective resolutions.

### Examples

**Example (Multiplication by $n$ as a chain complex).** The chain complex $K$ indexed by $\mathbb{N}$ with $X_1 = X_0 = \mathbb{Z}$, $d_{10} = n$ and $X_k = 0$ for $k \ge 2$ is built by the proposition from $d_0 = n$ and $d_k = 0$ for $k \ge 1$. By the theorem on single complexes, morphisms $K \to (\mathbb{Z}/n)[0]$ are the maps $\varepsilon : \mathbb{Z} \to \mathbb{Z}/n$ with $\varepsilon(n x) = 0$, which is all maps. So there are $n$ such morphisms. Morphisms $K \to \mathbb{Z}[0]$ are the $\varepsilon : \mathbb{Z} \to \mathbb{Z}$ with $\varepsilon \circ n = 0$, so only $\varepsilon = 0$. The augmentation of $K$ by the reduction $\mathbb{Z} \to \mathbb{Z}/n$ is $0 \to \mathbb{Z} \xrightarrow{n} \mathbb{Z} \to \mathbb{Z}/n$, which is exact. So $K$ is a free resolution of $\mathbb{Z}/n$.

**Example (A periodic complex).** The cochain complex indexed by $\mathbb{Z}$ with $X^k = \mathbb{Z}/4$ and $d^{k, k+1} = 2$ for every $k$ is a complex, since $2 \cdot 2 = 4 = 0$ in $\mathbb{Z}/4$. The same data with $\mathbb{Z}/8$ in place of $\mathbb{Z}/4$ is not a complex, because $4 \ne 0$ in $\mathbb{Z}/8$.

**Example (Polynomial differential forms).** Over $\mathbb{Q}$, the derivative $D : \mathbb{Q}[x] \to \mathbb{Q}[x]$ gives a cochain complex with $X^0 = X^1 = \mathbb{Q}[x]$, $d^{0,1} = D$ and all other objects zero. Its kernel at degree $0$ is the constants $\mathbb{Q}$, and $D$ is surjective, since $x^n = D(x^{n+1}/(n+1))$. Over $\mathbb{Z}$ the derivative is not surjective. Since $D(x^{n+1}) = (n+1) x^n$, the image $D(\mathbb{Z}[x])$ is spanned by the $(n+1)x^n$, and the cokernel is $\bigoplus_{n \ge 1} \mathbb{Z}/(n+1)$, generated by the classes of the $x^n$.

**Example (A shape of step 2).** The shape $\mathrm{up}'(2)$ on $\mathbb{Z}$ has $R(i, j)$ if and only if $j = i + 2$. A complex of this shape is the same as two cochain complexes, one on the even and one on the odd degrees.

**Counterexample (A relation that is not a shape).** On $\mathbb{N}$ the relation $i < j$ is not a complex shape, since $0$ has many successors. A complex for it would need a differential from $X_0$ to every $X_j$, and the next index would not be defined.

### The library around it

::: mathlib
`ComplexShape` · `Mathlib.Algebra.Homology.ComplexShape`

The structure has the field `Rel : ι → ι → Prop` and the two uniqueness conditions `next_eq` and `prev_eq`. `c.next i` and `c.prev j` are the next and the previous index, with the convention of the definition, and `next_eq'` identifies `c.next i` when `c.Rel i j`. `ComplexShape.up' a` and `ComplexShape.down' a` need `[Add α] [IsRightCancelAdd α]`. `c.symm` is the reversed shape.

<?decl ComplexShape?>
:::

::: mathlib
`ComplexShape.up` · `Mathlib.Algebra.Homology.ComplexShape`

`ComplexShape.up α` is `up' 1`, so `(up α).Rel i j ↔ i + 1 = j`. `ComplexShape.down α` is `down' 1`, with `Rel i j ↔ j + 1 = i`. The lemmas `up_Rel` and `down_Rel` unfold the relation.

<?decl ComplexShape.up?>
:::

::: mathlib
`HomologicalComplex` · `Mathlib.Algebra.Homology.HomologicalComplex`

The structure `HomologicalComplex V c` has the fields `X : ι → V`, `d : ∀ i j, X i ⟶ X j`, `shape : ¬ c.Rel i j → d i j = 0` and `d_comp_d' : c.Rel i j → c.Rel j k → d i j ≫ d j k = 0`. The simp lemma `d_comp_d` drops the hypotheses, as in the proposition. A morphism `HomologicalComplex.Hom` has the field `f` and the squares `comm'`, and `Hom.comm` holds for all `i j`. `hom_ext` reduces equality of morphisms to the components, and `Hom.isoOfComponents` builds an isomorphism from isomorphisms in each degree. `K.XIsoOfEq h` is the isomorphism `K.X p ≅ K.X q` for `h : p = q`.

<?decl HomologicalComplex?>
:::

::: mathlib
`ChainComplex` · `Mathlib.Algebra.Homology.HomologicalComplex`

`ChainComplex V α` is `HomologicalComplex V (ComplexShape.down α)`, and `CochainComplex V α` uses `up`. `ChainComplex.of X d sq` is the construction of the proposition, with `d n : X (n + 1) ⟶ X n`. `ChainComplex.mk` builds one step by step, the form used for resolutions.

<?decl ChainComplex?>
:::

::: mathlib
`HomologicalComplex.single` · `Mathlib.Algebra.Homology.Single`

`single V c j : V ⥤ HomologicalComplex V c` sends `A` to the complex with `A` in degree `j`. In degree `j` the object is `A` only up to the isomorphism `singleObjXSelf`, because the definition uses an `if` on `i = j`. The instances `instFullSingle` and `instFaithfulSingle` say that it is fully faithful. `ChainComplex.single₀` and `CochainComplex.single₀` are the special cases in degree `0`.

<?decl HomologicalComplex.single?>
:::

::: mathlib
`ChainComplex.toSingle₀Equiv` · `Mathlib.Algebra.Homology.Single`

The equivalence `(C ⟶ (single₀ V).obj X) ≃ {f : C.X 0 ⟶ X // C.d 1 0 ≫ f = 0}` of the theorem. `ChainComplex.fromSingle₀Equiv` is the dual statement, with no condition.

<?decl ChainComplex.toSingle₀Equiv?>
:::

::: mathlib
`CategoryTheory.Functor.mapHomologicalComplex` · `Mathlib.Algebra.Homology.Additive`

`F.mapHomologicalComplex c` needs `[F.PreservesZeroMorphisms]`. `NatTrans.mapHomologicalComplex` and `Equivalence.mapHomologicalComplex` are the other parts of the theorem, and `singleMapHomologicalComplex` is the isomorphism with single complexes.

<?decl CategoryTheory.Functor.mapHomologicalComplex?>
:::

::: mathlib
`ChainComplex.augment` · `Mathlib.Algebra.Homology.Augment`

`C.augment f w` takes `f : C.X 0 ⟶ X` and `w : C.d 1 0 ≫ f = 0`. `ChainComplex.truncate` is a functor, and `truncateAugment` and `augmentTruncate` are the two isomorphisms of the theorem. `CochainComplex.augment` is the version for cochain complexes.

<?decl ChainComplex.augment?>
:::

::: mathlib
`HomologicalComplex.op` · `Mathlib.Algebra.Homology.Opposite`

`K.op : HomologicalComplex Vᵒᵖ c.symm` with `d i j := (K.d j i).op`. `HomologicalComplex.unop` goes back, and `opEquivalence V c : (HomologicalComplex V c)ᵒᵖ ≌ HomologicalComplex Vᵒᵖ c.symm` is the proposition.

<?decl HomologicalComplex.op?>
:::

Common errors of a learner:

- `K.d i j` exists for all `i j`. A lemma that needs a nonzero differential must take `c.Rel i j` as a hypothesis.
- In `ChainComplex V ℕ`, `K.d 1 0` goes from degree `1` to degree `0`, and `K.d 0 1 = 0` by `shape`.
- `c.next i = i` when nothing follows `i`. So `c.next 0 = 0` for `down ℕ`, and the object `K.xNext 0` is `K.X 0`, not a zero object.
- `(single V c j).obj A` is not definitionally `A` in degree `j`. Use `singleObjXSelf`.

### Exercises

1. (A) Show that $\mathrm{up}(\mathbb{Z}).\mathrm{symm} = \mathrm{down}(\mathbb{Z})$, and compute $c.\mathrm{next}$ and $c.\mathrm{prev}$ for $c = \mathrm{down}(\mathbb{N})$ at $0$ and at $5$.
2. (A) Decide for which $m$ the data $X^k = \mathbb{Z}/m$, $d^{k,k+1} = 3$ for all $k \in \mathbb{Z}$ is a cochain complex.
3. (A) Let $K$ be $0 \to \mathbb{Z}/6 \xrightarrow{2} \mathbb{Z}/6$ in degrees $1$ and $0$. List the morphisms $K \to (\mathbb{Z}/3)[0]$ and $K \to (\mathbb{Z}/2)[0]$.
4. (B) Prove the dual half of the theorem on single complexes for cochain complexes indexed by $\mathbb{N}$: morphisms $A[0] \to K$ correspond to $\eta : A \to X^0$ with $d^{01} \circ \eta = 0$.
5. (B) Let $F = - \otimes_{\mathbb{Z}} \mathbb{Z}/2$ on abelian groups. Apply $F$ to the complex $\mathbb{Z} \xrightarrow{2} \mathbb{Z}$ and to $\mathbb{Z} \xrightarrow{3} \mathbb{Z}$, and compare the kernels and cokernels before and after.
6. (C) Show that the category of complexes of shape $c$ in an abelian category has kernels and cokernels computed in each degree. *Hint:* the kernel of $\varphi$ in degree $i$ is $\ker \varphi_i$, and the differential is induced. Section 2 states that this category is abelian.

### Notes and history

Chain complexes arose in algebraic topology, and their algebra is the subject of Cartan and Eilenberg (1956). The general complex shape is a design choice of Mathlib that removes equations between indices from the types.

The Mathlib Authors of `ComplexShape` and `HomologicalComplex` are Johan Commelin and Kim Morrison. The Mathlib Author of `Single`, `Additive` and `Augment` is Kim Morrison. The Mathlib Authors of `Opposite` are Johan Commelin, Amelia Livingston and Joël Riou.

### Reference

<?reference?>
