---
title: Tensor products, duals and the category of quadratic modules
kind: api
modules:
  - Mathlib.LinearAlgebra.BilinearForm.TensorProduct
  - Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
  - Mathlib.LinearAlgebra.QuadraticForm.TensorProduct.Isometries
  - Mathlib.LinearAlgebra.QuadraticForm.Dual
  - Mathlib.LinearAlgebra.QuadraticForm.QuadraticModuleCat
  - Mathlib.LinearAlgebra.QuadraticForm.QuadraticModuleCat.Monoidal
  - Mathlib.LinearAlgebra.QuadraticForm.QuadraticModuleCat.Symmetric
  - Mathlib.LinearAlgebra.CliffordAlgebra.CategoryTheory
explains:
  E2: [LinearMap.BilinForm.tensorDistrib_tmul, LinearMap.IsSymm.tmul, QuadraticForm.tensorDistrib_tmul, QuadraticForm.polarBilin_tmul, QuadraticForm.baseChange_tmul, baseChange_ext, QuadraticForm.tmul_comp_tensorComm, QuadraticForm.toDualProd, LinearMap.separatingLeft_dualProd, LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero]
  E1: auto
families: []
requires: [V08.C02, V08.C05, V24.C01, V24.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Tensor products, duals and the category of quadratic modules

### Overview

Sections 1 and 2 study one quadratic form at a time, and the orthogonal sum $Q_1 \oplus Q_2$ of two forms. This section adds the other operations of the algebra of forms. Two bilinear forms $B_1$ on $M_1$ and $B_2$ on $M_2$ give a bilinear form $B_1 \otimes B_2$ on $M_1 \otimes M_2$, and two quadratic forms give a quadratic form $Q_1 \otimes Q_2$ in the same way. A special case is the base change of a form from $R$ to an $R$-algebra $A$: the real form $x^2 + y^2$ becomes the complex form $z^2 + w^2$. The dual module gives a third operation: the module $M^* \times M$ carries the hyperbolic form $(f, x) \mapsto f(x)$.

The last modules collect quadratic modules into a category. An object is a module with a quadratic form, and a morphism is an isometry. With the tensor product of forms, this category is a symmetric monoidal category, and the Clifford algebra of Chapter 7 is a functor out of it. The section uses the tensor products of Chapter 2, the bilinear forms of Chapter 5, and the categories and monoidal categories of Volume 24, Chapters 1 and 7.

Fix a commutative ring $R$. Most results on quadratic forms of this section assume `[Invertible (2 : R)]`, because the construction of $Q_1 \otimes Q_2$ goes through the associated bilinear forms, and these need the factor $\frac12$.

### The library around it

#### The tensor product of bilinear forms

The module `Mathlib.LinearAlgebra.BilinearForm.TensorProduct` builds the bilinear form on a tensor product. The general map is `LinearMap.BilinMap.tensorDistrib R A`. It is a linear map from `BilinMap A M₁ N₁ ⊗[R] BilinMap R M₂ N₂` to `BilinMap A (M₁ ⊗[R] M₂) (N₁ ⊗[R] N₂)`, so it takes a tensor of two bilinear maps, not only a pair. The map is heterobasic: the left factor can be bilinear over an $R$-algebra $A$. On pure tensors it is given by `LinearMap.BilinMap.tensorDistrib_tmul`:

$$(B_1 \otimes B_2)(m_1 \otimes m_2, m_1' \otimes m_2') = B_1(m_1, m_1') \otimes B_2(m_2, m_2').$$

The shorthand `LinearMap.BilinMap.tmul B₁ B₂` is the image of `B₁ ⊗ₜ B₂`, so that dot notation `B₁.tmul B₂` works. For bilinear forms with values in the scalars, `LinearMap.BilinForm.tensorDistrib R A` and `LinearMap.BilinForm.tmul` compose with the isomorphism $A \otimes_R R \cong A$. Then `LinearMap.BilinForm.tensorDistrib_tmul` reads

$$(B_1 \otimes B_2)(m_1 \otimes m_2, m_1' \otimes m_2') = B_2(m_2, m_2') \cdot B_1(m_1, m_1').$$

The factor of $B_2$ comes first, as a scalar of $R$ that acts on the value in $A$. When $A = R$ this is the product $B_2(m_2, m_2') B_1(m_1, m_1')$.

**Theorem.** If $B_1$ and $B_2$ are symmetric, then $B_1 \otimes B_2$ is symmetric.

*Proof.* The two maps $(x, y) \mapsto (B_1 \otimes B_2)(x, y)$ and $(x, y) \mapsto (B_1 \otimes B_2)(y, x)$ are bilinear on $M_1 \otimes M_2$. So they are equal when they agree on pairs of pure tensors. On these pairs the values are $B_2(m_2, m_2') B_1(m_1, m_1')$ and $B_2(m_2', m_2) B_1(m_1', m_1)$, and these agree by the symmetry of each factor. $\square$

In Lean this is `LinearMap.IsSymm.tmul` for forms, and `LinearMap.BilinMap.tmul_isSymm` for bilinear maps, with the symmetry stated as a function `∀ x y, B x y = B y x`.

The base change of a bilinear form is the tensor product with the multiplication of $A$, the bilinear form `LinearMap.mul A A`. The result `LinearMap.BilinForm.baseChange A B` is an $A$-bilinear form on $A \otimes_R M$ with `LinearMap.BilinForm.baseChange_tmul`: $B_A(a \otimes m, a' \otimes m') = B(m, m') \cdot a a'$. The base change of a symmetric form is symmetric (`LinearMap.BilinForm.IsSymm.baseChange`). The base change of $0$ is $0$ (`LinearMap.BilinForm.baseChange_zero`). The converse needs that $R$ acts faithfully on $A$: under `[FaithfulSMul R A]`, `LinearMap.BilinForm.baseChange_eq_zero_iff` says that $B_A = 0$ exactly when $B = 0$. The same constructions for bilinear maps are `LinearMap.BilinMap.baseChange`, `LinearMap.BilinMap.baseChange_tmul` and `LinearMap.BilinMap.baseChange_isSymm`.

For finite projective modules over a commutative ring, the map $B_1 \otimes B_2 \mapsto B_1 \otimes B_2$ is an isomorphism. This is `LinearMap.BilinForm.tensorDistribEquiv R`, a linear equivalence from `BilinForm R M₁ ⊗[R] BilinForm R M₂` to `BilinForm R (M₁ ⊗[R] M₂)`. Its proof writes a bilinear form on $M$ as a linear form on $M \otimes M$ and uses the isomorphism $(M_1 \otimes M_1)^* \otimes (M_2 \otimes M_2)^* \cong (M_1 \otimes M_1 \otimes M_2 \otimes M_2)^*$ of Chapter 2, Section 3 (`TensorProduct.dualDistribEquiv`). The lemma `LinearMap.BilinForm.tensorDistribEquiv_apply` says that it agrees with `tensorDistrib R R`. For $M_1 = R^m$ and $M_2 = R^n$ the equivalence says that each bilinear form on $R^{mn}$ is a sum of tensor products: in matrix terms, each $mn \times mn$ matrix is a sum of Kronecker products.

#### The tensor product of quadratic forms

The module `Mathlib.LinearAlgebra.QuadraticForm.TensorProduct` repeats the construction for quadratic maps. The map `QuadraticMap.tensorDistrib R A` takes the associated bilinear forms of the two factors, forms their tensor product, and takes the quadratic form of the result. The values on pure tensors are simple (`QuadraticMap.tensorDistrib_tmul` and `QuadraticForm.tensorDistrib_tmul`):

$$(Q_1 \otimes Q_2)(m_1 \otimes m_2) = Q_2(m_2) \cdot Q_1(m_1).$$

*Proof.* By definition $(Q_1 \otimes Q_2)(x) = (\beta_1 \otimes \beta_2)(x, x)$, where $\beta_i$ is the associated form of $Q_i$, with $\beta_i(m, m) = Q_i(m)$. At $x = m_1 \otimes m_2$ the rule for bilinear forms gives $\beta_2(m_2, m_2) \beta_1(m_1, m_1) = Q_2(m_2) Q_1(m_1)$. $\square$

The value at a sum of pure tensors involves cross terms, and these come from the polar forms. The dot notation is `Q₁.tmul Q₂` (`QuadraticForm.tmul`). The associated form of a tensor product is the tensor product of the associated forms (`QuadraticForm.associated_tmul`). For the polar form there is a factor:

$$\operatorname{polar}_{Q_1 \otimes Q_2} = \tfrac12 \operatorname{polar}_{Q_1} \otimes \operatorname{polar}_{Q_2}.$$

*Proof.* Write $p_i = \operatorname{polar}_{Q_i}$ and $\beta_i = \frac12 p_i$. The polar form of a quadratic form is twice its associated form, so $\operatorname{polar}_{Q_1 \otimes Q_2} = 2 (\beta_1 \otimes \beta_2) = 2 \cdot \frac12 \cdot \frac12 (p_1 \otimes p_2) = \frac12 (p_1 \otimes p_2)$. $\square$

This is `QuadraticForm.polarBilin_tmul`, stated with `polarBilin` and the scalar `⅟(2 : A)`.

The base change of a quadratic form is the tensor product with the square form `QuadraticMap.sq` on $A$. The form `QuadraticForm.baseChange A Q` on $A \otimes_R M$ has the value $Q(m) \cdot a^2$ at $a \otimes m$ (`QuadraticForm.baseChange_tmul`), and its associated form and its polar form are the base changes of those of $Q$ (`QuadraticForm.associated_baseChange` and `QuadraticForm.polarBilin_baseChange`).

**Theorem.** Let $Q$ and $Q'$ be quadratic maps on $A \otimes_R M$ that agree at $1 \otimes m$ for each $m \in M$. Then $Q = Q'$. This holds with no condition on $2$.

*Proof.* First $Q(a \otimes m) = Q(a \cdot (1 \otimes m)) = a^2 Q(1 \otimes m)$, and the same holds for $Q'$, so the two maps agree on all pure tensors. Next compare the polar forms. They are $A$-bilinear on $A \otimes M$, and the elements $1 \otimes m$ generate $A \otimes M$ as an $A$-module. So it suffices to compare them on pairs $(1 \otimes m, 1 \otimes m')$. There $\operatorname{polar}_Q(1 \otimes m, 1 \otimes m') = Q(1 \otimes (m + m')) - Q(1 \otimes m) - Q(1 \otimes m')$, and the same expression for $Q'$ has the same value. So the polar forms are equal. Now induct on $x \in A \otimes M$. For a pure tensor the claim is the first step. For a sum, $Q(x + y) = Q(x) + Q(y) + \operatorname{polar}_Q(x, y)$, and each term agrees with the term for $Q'$. $\square$

This is the extensionality lemma `baseChange_ext`, at the root of the namespace. It says that a base change of a quadratic map is unique when it exists, even in characteristic $2$, where `QuadraticForm.baseChange` is not defined.

#### Isometries of tensor products

The module `Mathlib.LinearAlgebra.QuadraticForm.TensorProduct.Isometries` shows that the standard isomorphisms of Chapter 2 preserve the tensor product of forms. Each isomorphism comes in three forms, with one naming pattern. For the swap of the factors, the theorem `QuadraticForm.tmul_comp_tensorComm` is an equality of forms after composition with `TensorProduct.comm`, the lemma `QuadraticForm.tmul_tensorComm_apply` states it at a point, and the definition `QuadraticForm.tensorComm` packages the linear map as an isometry equivalence. The associator follows the same pattern. For the unitors the theorems are `QuadraticForm.comp_tensorLId_eq` and `QuadraticForm.comp_tensorRId_eq`.

| Lean name | Statement |
|---|---|
| `QuadraticForm.tensorComm Q₁ Q₂` | $Q_1 \otimes Q_2 \cong Q_2 \otimes Q_1$ by `TensorProduct.comm` |
| `QuadraticForm.tensorAssoc Q₁ Q₂ Q₃` | $(Q_1 \otimes Q_2) \otimes Q_3 \cong Q_1 \otimes (Q_2 \otimes Q_3)$ by `TensorProduct.assoc` |
| `QuadraticForm.tensorLId Q` | $\mathrm{sq} \otimes Q \cong Q$ by `TensorProduct.lid` |
| `QuadraticForm.tensorRId Q` | $Q \otimes \mathrm{sq} \cong Q$ by `TensorProduct.rid` |
| `QuadraticMap.Isometry.tmul f g` | $f \otimes g$ is an isometry $Q_1 \otimes Q_3 \to Q_2 \otimes Q_4$ |

The proofs share one idea. Two quadratic forms are equal when their associated forms are equal, because $Q \mapsto \beta_Q$ is injective when $2$ is invertible. The associated forms are bilinear, so a check on pure tensors suffices, and there the statement is the commutativity or the associativity of multiplication in $R$. For example, `QuadraticForm.tmul_comp_tensorComm` reduces to $Q_1(m_1) Q_2(m_2) = Q_2(m_2) Q_1(m_1)$. The inverse of `tensorComm Q₁ Q₂` is `tensorComm Q₂ Q₁` (`QuadraticForm.tensorComm_symm`), and each of these equivalences has `apply` and `symm_apply` lemmas that reduce it to the underlying linear equivalence.

#### The hyperbolic form on $M^* \times M$

The module `Mathlib.LinearAlgebra.QuadraticForm.Dual` defines the hyperbolic form of a module. The quadratic form `QuadraticForm.dualProd R M` on $M^* \times M$ is $(f, x) \mapsto f(x)$. Its companion bilinear form is `LinearMap.dualProd R M`:

$$B((f, x), (g, y)) = f(y) + g(x).$$

It is symmetric (`LinearMap.isSymm_dualProd`), and its quadratic form is twice `dualProd`, not `dualProd` itself (`LinearMap.dualProd.toQuadraticForm`). For $M = R$ the hyperbolic form is $(a, x) \mapsto a x$, the hyperbolic plane.

**Theorem.** The form `LinearMap.dualProd R M` is left separating exactly when the evaluation map $M \to M^{**}$ is injective.

*Proof sketch.* The form sends $(f, x)$ to the linear form $(g, y) \mapsto f(y) + g(x)$ on $M^* \times M$. Under the isomorphism $(M^* \times M)^* \cong M^{**} \times M^*$, this map is $(f, x) \mapsto (\operatorname{ev}(x), f)$, the product of the evaluation and the identity. A product map is injective exactly when each factor is injective, and the identity is injective. $\square$

This is `LinearMap.separatingLeft_dualProd`, with the evaluation map `Module.Dual.eval R M`. For a vector space the evaluation is injective, so the hyperbolic form is nondegenerate. A linear equivalence $f : M \cong N$ gives an isometry equivalence of the hyperbolic forms (`QuadraticForm.dualProdIsometry`), and the hyperbolic form of a product is the orthogonal sum of the hyperbolic forms (`QuadraticForm.dualProdProdIsometry`).

The map `QuadraticForm.toDualProd Q` is an isometry from $Q \oplus (-Q)$ on $M \times M$ to the hyperbolic form. It sends $(x, y)$ to $(\beta(x + y, \cdot), x - y)$, where $\beta$ is the associated form of $Q$. The check is short: $\beta(x + y, x - y) = \beta(x, x) - \beta(y, y) = Q(x) - Q(y)$, by the symmetry of $\beta$. So the orthogonal sum of a form and its negative always maps isometrically to a hyperbolic form.

The same module holds a lemma on obtuse vectors, `LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero`.

**Theorem.** Let $R$ be a strictly ordered commutative ring, $B$ a bilinear form with positive definite quadratic form, and $f$ a linear form. Let $(v_i)$ be vectors with $f(v_i) > 0$ for all $i$ and $B(v_i, v_j) \le 0$ for $i \ne j$. Then the $v_i$ are linearly independent.

*Proof.* Let $\sum_i c_i v_i = 0$ be a finite relation. Split the indices by the sign of $c_i$ and put $x = \sum_{c_i > 0} c_i v_i$ and $y = \sum_{c_i < 0} (-c_i) v_i$. Then $x = y$. The value $B(x, y)$ is a sum of terms $c_i (-c_j) B(v_i, v_j)$ with $i \ne j$, and each term is at most $0$. So $Q(x) = B(x, x) = B(x, y) \le 0$, and positive definiteness gives $x = 0$. Now $0 = f(x) = \sum_{c_i > 0} c_i f(v_i)$ is a sum of positive terms, so no $c_i$ is positive. The same argument for $y$ shows that no $c_i$ is negative. $\square$

#### The category of quadratic modules

The module `Mathlib.LinearAlgebra.QuadraticForm.QuadraticModuleCat` defines the category `QuadraticModuleCat R`. An object extends an object of `ModuleCat R` by a field `form`, a quadratic form on the carrier. The constructor `QuadraticModuleCat.of Q` takes a module and a form. A morphism is a structure `QuadraticModuleCat.Hom V W` with one field, an isometry `V.form →qᵢ W.form`. The wrapper keeps the composition of the category apart from the composition of isometries. The two directions are `QuadraticModuleCat.Hom.toIsometry` and `QuadraticModuleCat.ofHom`, and `QuadraticModuleCat.toIsometry_comp` says that `(f ≫ g).toIsometry = g.toIsometry.comp f.toIsometry`, with the order reversed. Two morphisms are equal when their isometries are equal (`QuadraticModuleCat.hom_ext`). The forgetful functor to `ModuleCat R` is the instance `QuadraticModuleCat.hasForgetToModule`, with `QuadraticModuleCat.forget₂_map`.

Isomorphisms in the category are isometry equivalences. The function `QuadraticModuleCat.ofIso` turns an isometry equivalence into an isomorphism, and `CategoryTheory.Iso.toIsometryEquiv` goes back. Both respect identities, inverses and composites (`QuadraticModuleCat.ofIso_trans`, `CategoryTheory.Iso.toIsometryEquiv_trans`).

When $2$ is invertible, the module `Mathlib.LinearAlgebra.QuadraticForm.QuadraticModuleCat.Monoidal` makes the category monoidal (`QuadraticModuleCat.instMonoidalCategory`). The tensor of objects is `of (X.form.tmul Y.form)`, the unit is `of (sq (R := R))`, and the associator and the unitors are `ofIso` of the isometries of the table above. The coherence conditions are not checked by hand: the structure is induced from the monoidal structure of `ModuleCat R` along the forgetful functor, which is faithful. So the forgetful functor is monoidal, and lemmas such as `QuadraticModuleCat.toModuleCat_tensor` and `QuadraticModuleCat.forget₂_map_associator_hom` say that the tensor and the associator lie over those of modules. The lemmas `QuadraticModuleCat.toIsometry_tensorHom` and `QuadraticModuleCat.hom_hom_associator` give the underlying isometries. The module `Mathlib.LinearAlgebra.QuadraticForm.QuadraticModuleCat.Symmetric` adds the braiding `ofIso (tensorComm X.form Y.form)` and the instance `QuadraticModuleCat.instSymmetricCategory`, again by transport along the faithful forgetful functor.

The module `Mathlib.LinearAlgebra.CliffordAlgebra.CategoryTheory` defines the functor `QuadraticModuleCat.cliffordAlgebra` from `QuadraticModuleCat R` to `AlgCat R`. It sends a quadratic module to its Clifford algebra, and an isometry $f$ to the algebra map `CliffordAlgebra.map f` of Chapter 7 (`QuadraticModuleCat.cliffordAlgebra_map`). Functoriality is the uniqueness part of the universal property of the Clifford algebra.

#### Common errors

1. The rule `QuadraticForm.tensorDistrib_tmul` gives `Q₂ m₂ • Q₁ m₁`, with the right factor first, not `Q₁ m₁ * Q₂ m₂`. When $A = R$, a rewrite with `smul_eq_mul` and `mul_comm` is often needed.
2. `QuadraticForm.tmul`, `QuadraticForm.baseChange` and the monoidal structure on `QuadraticModuleCat R` need an instance `[Invertible (2 : R)]` in the context. Over a ring such as $\mathbb{Z}$ these declarations do not apply. The lemma `baseChange_ext` needs no such instance.
3. `QuadraticForm.toDualProd Q` is an isometry `→qᵢ`, a form-preserving linear map. The library does not yet prove that it is an equivalence.

### Exercises

1. (A) Let $Q_1 = a x^2 + b y^2$ on $R^2$ and $Q_2 = c u^2 + d v^2$ on $R^2$. Show that $Q_1 \otimes Q_2$ is the diagonal form with coefficients $a c, a d, b c, b d$ in the basis $e_i \otimes f_j$.
2. (A) Show that the base change of $x^2 + y^2$ from $\mathbb{R}$ to $\mathbb{C}$ is isometric to the hyperbolic plane $(a, z) \mapsto a z$ over $\mathbb{C}$.
3. (B) Let $Q_1$ and $Q_2$ be real diagonal forms of signatures $(p_1, n_1)$ and $(p_2, n_2)$ with no zero coefficients. Compute the signature of $Q_1 \otimes Q_2$ with Section 2.
4. (B) Show that the hyperbolic form on $\mathbb{Z}^* \times \mathbb{Z}$ is not isometric to an orthogonal sum $a x^2 + b y^2$ over $\mathbb{Z}$. Hint: compare the determinants of the Gram matrices of the polar forms.
5. (B) Show that at most $n$ vectors of $\mathbb{R}^n$ lie in an open half space and have pairwise obtuse or right angles. Give $n$ such vectors with pairwise obtuse angles.
6. (C) Show that `QuadraticForm.toDualProd Q` is bijective when $Q$ is nondegenerate and $M$ is finite dimensional over a field of characteristic not $2$.

### Reference

<?reference?>
