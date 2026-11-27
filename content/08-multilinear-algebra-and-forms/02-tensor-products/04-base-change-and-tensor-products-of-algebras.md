---
title: Base change and tensor products of algebras
kind: theory
modules:
  - Mathlib.LinearAlgebra.TensorProduct.Tower
  - Mathlib.RingTheory.TensorProduct.Basic
  - Mathlib.RingTheory.TensorProduct.Maps
  - Mathlib.RingTheory.TensorProduct.Free
  - Mathlib.RingTheory.IsTensorProduct
explains:
  E3: [Algebra.TensorProduct.lift, LinearMap.baseChange, IsBaseChange]
  E2: [Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.productMap, Algebra.TensorProduct.basis, Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul, TensorProduct.isBaseChange, IsBaseChange.lift, IsBaseChange.lift_eq, LinearMap.toMatrix_baseChange, TensorProduct.AlgebraTensorModule.cancelBaseChange]
  E1: auto
families: []
requires: [V07.C01, V07.C02, V06.C01, V06.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Base change and tensor products of algebras

### Overview

A real vector space $V$ gives a complex vector space $\mathbb{C} \otimes_{\mathbb{R}} V$ of the same dimension. This is the extension of scalars, or base change. For each algebra $S$ over a commutative ring $R$, the tensor product $S \otimes_R M$ is an $S$-module. If $A$ and $B$ are both $R$-algebras, $A \otimes_R B$ is again an $R$-algebra, with $(a \otimes b)(a' \otimes b') = a a' \otimes b b'$. Algebra maps out of $A \otimes_R B$ are pairs of algebra maps with commuting images. The section uses Sections 1 to 3 of this chapter, Volume 7, Chapters 1 and 2, and Volume 6, Chapters 1 and 8.

### Definitions

Fix a commutative ring $R$ and an $R$-algebra $S$. All unmarked tensor products are over $R$.

**Definition (Extension of scalars).** For an $R$-module $M$, the module $S \otimes M$ is an $S$-module with $s' \cdot (s \otimes m) = s' s \otimes m$. The map $\iota : M \to S \otimes M$, $\iota(m) = 1 \otimes m$, is $R$-linear. For an $R$-linear map $f : M \to N$, the base change of $f$ is $f_S = \mathrm{id}_S \otimes f : S \otimes M \to S \otimes N$.

The action exists: for fixed $s'$, multiplication by $s'$ is an $R$-linear map $\mu_{s'} : S \to S$, and $\mu_{s'} \otimes \mathrm{id}_M$ is its action on $S \otimes M$ by Section 2. The module rules follow from functoriality, and $f_S$ is $S$-linear.

**Definition (Tensor product of algebras).** Let $A$ and $B$ be $R$-algebras. The algebra $A \otimes B$ is the module $A \otimes B$ with the product given on pure tensors by $(a \otimes b)(a' \otimes b') = a a' \otimes b b'$ and the unit $1 \otimes 1$. The maps $\iota_A(a) = a \otimes 1$ and $\iota_B(b) = 1 \otimes b$ are the inclusions.

**Definition (Base change, abstract form).** An $R$-linear map $g : M \to N$ to an $S$-module $N$ is a base change of $M$ to $S$ if the $S$-linear map $S \otimes M \to N$, $s \otimes m \mapsto s \cdot g(m)$, is bijective.

::: mathlib
`LinearMap.baseChange` · `Mathlib.LinearAlgebra.TensorProduct.Tower`

For an `R`-algebra `A` and `f : M →ₗ[R] N`, the map `f.baseChange A : A ⊗[R] M →ₗ[A] A ⊗[R] N`, with `LinearMap.baseChange_tmul` for `a ⊗ₜ x ↦ a ⊗ₜ f x`. The file also holds `TensorProduct.AlgebraTensorModule.cancelBaseChange`, the isomorphism $M \otimes_A (A \otimes_R N) \cong M \otimes_R N$ that makes base change transitive.

<?decl LinearMap.baseChange?>
:::

::: mathlib
`IsBaseChange` · `Mathlib.RingTheory.IsTensorProduct`

The predicate `IsBaseChange S f` for `f : M →ₗ[R] N`, defined through `IsTensorProduct`: the induced map from `S ⊗[R] M` is bijective. The lemma `TensorProduct.isBaseChange` says that `TensorProduct.mk R S M 1`, the map $m \mapsto 1 \otimes m$, is a base change.

<?decl IsBaseChange?>
<?decl TensorProduct.isBaseChange?>
:::

### Theorems and proofs

**Theorem (Universal property of extension of scalars).** Let $P$ be an $S$-module, seen as an $R$-module through $R \to S$. For each $R$-linear map $h : M \to P$ there is exactly one $S$-linear map $\bar h : S \otimes M \to P$ with $\bar h(1 \otimes m) = h(m)$. It is $\bar h(s \otimes m) = s \cdot h(m)$.

*Proof.* The map $(s, m) \mapsto s \cdot h(m)$ is $R$-bilinear, so it induces an $R$-linear map $\bar h$ by Section 1. It is $S$-linear: $\bar h(s'(s \otimes m)) = s' s \cdot h(m) = s' \cdot \bar h(s \otimes m)$ on pure tensors, and both sides are additive. Uniqueness: an $S$-linear map with $\bar h(1 \otimes m) = h(m)$ satisfies $\bar h(s \otimes m) = \bar h(s \cdot (1 \otimes m)) = s \cdot h(m)$, and pure tensors generate. $\square$

So $\operatorname{Hom}_S(S \otimes M, P) \cong \operatorname{Hom}_R(M, P)$, and $\iota : M \to S \otimes M$ is a base change in the abstract sense.

::: mathlib
`IsBaseChange.lift` · `Mathlib.RingTheory.IsTensorProduct`

For `h : IsBaseChange S f` and an `R`-linear map `g : M →ₗ[R] Q` to an `S`-module `Q`, the `S`-linear map `h.lift g : N →ₗ[S] Q`, with `IsBaseChange.lift_eq` for `h.lift g (f x) = g x`.

<?decl IsBaseChange.lift?>
<?decl IsBaseChange.lift_eq?>
:::

**Theorem (Bases under base change).** If $M$ is free with basis $(e_i)_{i \in I}$, then $S \otimes M$ is a free $S$-module with basis $(1 \otimes e_i)_{i \in I}$. If $f : M \to N$ has the matrix $A$ in bases $(e_j)$ and $(e'_i)$, then $f_S$ has the matrix $\varphi(A)$ in the bases $(1 \otimes e_j)$ and $(1 \otimes e'_i)$, where $\varphi : R \to S$ is the structure map applied to each entry.

*Proof.* The basis gives $M \cong R^{(I)}$. By Section 2 the tensor product commutes with direct sums, so $S \otimes M \cong S \otimes R^{(I)} \cong (S \otimes R)^{(I)} \cong S^{(I)}$, and the composite sends $s \otimes e_i$ to $s$ in the place $i$. This map is $S$-linear, so the $1 \otimes e_i$ form an $S$-basis. For the matrix, $f_S(1 \otimes e_j) = 1 \otimes \sum_i A_{i j} e'_i = \sum_i \varphi(A_{i j}) (1 \otimes e'_i)$. $\square$

::: mathlib
`Algebra.TensorProduct.basis` · `Mathlib.RingTheory.TensorProduct.Free`

From `b : Basis ι R M`, the `A`-basis `Algebra.TensorProduct.basis A b` of `A ⊗[R] M`, with `Algebra.TensorProduct.basis_apply`: the vector `i` is `1 ⊗ₜ b i`. The rule for matrices is `LinearMap.toMatrix_baseChange`: the matrix of `f.baseChange A` is the matrix of `f` mapped by `algebraMap R A`.

<?decl Algebra.TensorProduct.basis?>
<?decl LinearMap.toMatrix_baseChange?>
:::

**Theorem (The algebra $A \otimes B$).** The product of the definition exists, and it makes $A \otimes B$ an $R$-algebra. The inclusions $\iota_A$ and $\iota_B$ are algebra maps, and their images commute: $\iota_A(a) \, \iota_B(b) = a \otimes b = \iota_B(b) \, \iota_A(a)$.

*Proof.* For fixed $a, b$, the map $(a', b') \mapsto a a' \otimes b b'$ is bilinear, so it gives a linear map $L_{a, b} : A \otimes B \to A \otimes B$. The map $(a, b) \mapsto L_{a, b}$ is bilinear too, so it gives a linear map $A \otimes B \to \operatorname{End}(A \otimes B)$. This defines a bilinear product $x y$ with the required value on pure tensors. Associativity and the unit rule are equalities of multilinear maps, so a check on pure tensors suffices. The algebra map is $r \mapsto r \cdot 1 \otimes 1$. The last claims follow from $(a \otimes 1)(1 \otimes b) = a \otimes b = (1 \otimes b)(a \otimes 1)$. $\square$

::: mathlib
`Algebra.TensorProduct.tmul_mul_tmul` · `Mathlib.RingTheory.TensorProduct.Basic`

The rule `a₁ ⊗ₜ b₁ * a₂ ⊗ₜ b₂ = (a₁ * a₂) ⊗ₜ (b₁ * b₂)`. The algebra structure on `A ⊗[R] B` is an instance. The inclusions are the algebra maps `Algebra.TensorProduct.includeLeft` and `Algebra.TensorProduct.includeRight`.

<?decl Algebra.TensorProduct.tmul_mul_tmul?>
<?decl Algebra.TensorProduct.includeLeft?>
<?decl Algebra.TensorProduct.includeRight?>
:::

**Theorem (Universal property of $A \otimes B$).** Let $C$ be an $R$-algebra and let $f : A \to C$ and $g : B \to C$ be algebra maps with $f(a) g(b) = g(b) f(a)$ for all $a, b$. Then there is exactly one algebra map $h : A \otimes B \to C$ with $h \circ \iota_A = f$ and $h \circ \iota_B = g$. It is $h(a \otimes b) = f(a) g(b)$.

*Proof.* The map $(a, b) \mapsto f(a) g(b)$ is bilinear, so it gives a linear map $h$. It sends $1 \otimes 1$ to $1$. It is multiplicative on pure tensors: $h(a a' \otimes b b') = f(a) f(a') g(b) g(b') = f(a) g(b) f(a') g(b')$, where the second step moves $f(a')$ past $g(b)$ by the hypothesis. Both sides of $h(x y) = h(x) h(y)$ are bilinear in $(x, y)$, so the rule holds for all $x, y$. Uniqueness: an algebra map $h'$ with these restrictions has $h'(a \otimes b) = h'(\iota_A(a) \iota_B(b)) = f(a) g(b)$, and pure tensors generate. $\square$

**Corollary (Coproduct).** If $A$, $B$ and $C$ are commutative, the hypothesis holds always. So $A \otimes B$, with $\iota_A$ and $\iota_B$, is the coproduct of $A$ and $B$ in the category of commutative $R$-algebras.

::: mathlib
`Algebra.TensorProduct.lift` · `Mathlib.RingTheory.TensorProduct.Maps`

The map `lift f g hfg : A ⊗[R] B →ₐ[S] C` for `f : A →ₐ[S] C`, `g : B →ₐ[R] C` and `hfg : ∀ x y, Commute (f x) (g y)`, with `Algebra.TensorProduct.lift_tmul`: the value at `a ⊗ₜ b` is `f a * g b`. For a commutative target, `Algebra.TensorProduct.productMap f g` needs no hypothesis.

<?decl Algebra.TensorProduct.lift?>
<?decl Algebra.TensorProduct.productMap?>
:::

### Examples

**Example ($\mathbb{C} \otimes_{\mathbb{R}} \mathbb{C} \cong \mathbb{C} \times \mathbb{C}$).** The maps $f(z) = (z, z)$ and $g(w) = (w, \bar w)$ are $\mathbb{R}$-algebra maps $\mathbb{C} \to \mathbb{C} \times \mathbb{C}$, and the target is commutative. The corollary gives an $\mathbb{R}$-algebra map $h(z \otimes w) = (z w, z \bar w)$. By the basis theorem of Section 3, $\mathbb{C} \otimes_{\mathbb{R}} \mathbb{C}$ has the real basis $1 \otimes 1$, $1 \otimes i$, $i \otimes 1$, $i \otimes i$. Their images are $(1, 1)$, $(i, -i)$, $(i, i)$, $(-1, 1)$. In real coordinates these are $(1, 0, 1, 0)$, $(0, 1, 0, -1)$, $(0, 1, 0, 1)$, $(-1, 0, 1, 0)$. The first and the last are independent in the coordinates $1$ and $3$, and the other two in the coordinates $2$ and $4$. So $h$ is bijective, and $\mathbb{C} \otimes_{\mathbb{R}} \mathbb{C} \cong \mathbb{C} \times \mathbb{C}$ as algebras. The tensor product of two fields is not a field here: the element $\frac12 (1 \otimes 1 + i \otimes i)$ maps to $(0, 1)$, a zero divisor and an idempotent.

**Example ($\mathbb{Q} \otimes_{\mathbb{Z}} A = 0$ for finite $A$).** Let $A$ be a finite abelian group of order $n$, so $n a = 0$ for each $a \in A$. For $q \in \mathbb{Q}$, $q \otimes a = \frac{q}{n} n \otimes a = \frac{q}{n} \otimes n a = 0$. Pure tensors generate, so $\mathbb{Q} \otimes_{\mathbb{Z}} A = 0$. The base change to $\mathbb{Q}$ forgets all torsion.

**Counterexample (The commuting hypothesis is needed).** Let $\mathbb{H}$ be the real quaternions, and take $A = B = C = \mathbb{H}$ and $f = g = \mathrm{id}$. Assume that an algebra map $h : \mathbb{H} \otimes_{\mathbb{R}} \mathbb{H} \to \mathbb{H}$ restricts to $f$ and $g$. In $\mathbb{H} \otimes \mathbb{H}$, $i \otimes j = (i \otimes 1)(1 \otimes j) = (1 \otimes j)(i \otimes 1)$. Apply $h$ to both products: $h(i \otimes j) = i j = k$ and $h(i \otimes j) = j i = -k$. So $k = -k$, which is false. No such $h$ exists, and the map $a \otimes b \mapsto a b$ is linear but not multiplicative.

### The library around it

Mathlib states most results on base change with `IsBaseChange`, so that a localization can be used where a tensor product is expected. The universal property of the algebra is also an equivalence, `Algebra.TensorProduct.liftEquiv`.

### Exercises

1. (A) Show that $\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R}^n \cong \mathbb{C}^n$ as complex vector spaces. Hint: the basis theorem.
2. (A) Compute $\mathbb{Z}/2 \otimes_{\mathbb{Z}} \mathbb{Z}[x]$ as a ring. Hint: $\mathbb{Z}[x]$ is free with basis $x^k$.
3. (A) Show that $\mathbb{Q} \otimes_{\mathbb{Z}} \mathbb{Q} \cong \mathbb{Q}$. Hint: $\frac{a}{b} \otimes \frac{c}{d} = \frac{a c}{b d} \otimes 1$.
4. (B) Show that $R[x] \otimes_R R[y] \cong R[x, y]$ as $R$-algebras. Hint: the coproduct property and the bases.
5. (B) Show that $(f \circ g)_S = f_S \circ g_S$ and that $f_S$ is injective when $f$ is split injective. Hint: functoriality from Section 2.
6. (B) Show that $\mathbb{Q}(\sqrt 2) \otimes_{\mathbb{Q}} \mathbb{Q}(\sqrt 2) \cong \mathbb{Q}(\sqrt 2) \times \mathbb{Q}(\sqrt 2)$. Hint: copy the example with $\sqrt 2 \mapsto -\sqrt 2$.
7. (C) Show that $\mathbb{Z}/m \otimes_{\mathbb{Z}} \mathbb{Z}/n \cong \mathbb{Z}/\gcd(m, n)$ as rings, not only as groups. Hint: the map of Section 1 is $\bar a \otimes \bar b \mapsto \overline{a b}$.

### Notes and history

The tensor product of two field extensions is a product of fields when one of them is finite and separable; Volume 11 uses this fact.

### Reference

<?reference?>
