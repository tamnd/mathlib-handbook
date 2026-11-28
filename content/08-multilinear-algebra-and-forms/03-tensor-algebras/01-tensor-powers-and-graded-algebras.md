---
title: Tensor powers and graded algebras
kind: theory
modules:
  - Mathlib.LinearAlgebra.PiTensorProduct.Basic
  - Mathlib.LinearAlgebra.PiTensorProduct.Basis
  - Mathlib.LinearAlgebra.TensorPower.Basic
  - Mathlib.Algebra.DirectSum.Basic
  - Mathlib.Algebra.DirectSum.Module
  - Mathlib.Algebra.DirectSum.Algebra
  - Mathlib.Algebra.DirectSum.Ring
  - Mathlib.Algebra.DirectSum.Decomposition
  - Mathlib.Algebra.GradedMonoid
  - Mathlib.LinearAlgebra.DirectSum.Basis
  - Mathlib.LinearAlgebra.DirectSum.Finite
explains:
  E3: [PiTensorProduct, PiTensorProduct.lift, TensorPower, DirectSum]
  E2: [PiTensorProduct.tprod, Basis.piTensorProduct, TensorPower.mulEquiv, DirectSum.lof, DirectSum.toModule, GradedMonoid.GMonoid, SetLike.GradedMonoid, DirectSum.Decomposition]
  E1: auto
families: []
requires: [V08.C01, V08.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Tensor powers and graded algebras

### Overview

Chapter 2 builds the tensor product of two modules. This section builds the tensor product of a family $(M_i)_{i \in \iota}$, which turns each multilinear map of Chapter 1 into a linear map. When all the $M_i$ are one module $M$ and $\iota = \{1, \dots, n\}$, the product is the tensor power $M^{\otimes n}$.

To collect all the powers into one ring, the section then defines direct sums and graded algebras. Throughout, $R$ is a commutative ring.

### Definitions

**Definition (Tensor product of a family).** Let $(M_i)_{i \in \iota}$ be a family of $R$-modules. Let $F$ be the free $R$-module on the set $\prod_i M_i$. Let $K \subseteq F$ be the submodule spanned by the elements
$$[f[i := x + y]] - [f[i := x]] - [f[i := y]], \qquad [f[i := r x]] - r [f[i := x]],$$
for all $f \in \prod_i M_i$, $i \in \iota$, $x, y \in M_i$ and $r \in R$. Here $f[i := x]$ is $f$ with the coordinate $i$ replaced by $x$. The tensor product is $\bigotimes_i M_i = F / K$. The class of $[f]$ is written $\bigotimes_i f_i$ and is a pure tensor.

The relations say that the map $\operatorname{tprod} : \prod_i M_i \to \bigotimes_i M_i$, $f \mapsto \bigotimes_i f_i$, is multilinear.

::: mathlib
`PiTensorProduct` · `Mathlib.LinearAlgebra.PiTensorProduct.Basic`

The type `⨂[R] i, s i` for a family `s : ι → Type*` of modules over a commutative semiring `R`.

<?decl PiTensorProduct?>
:::

::: mathlib
`PiTensorProduct.tprod` · `Mathlib.LinearAlgebra.PiTensorProduct.Basic`

The multilinear map `tprod R : MultilinearMap R s (⨂[R] i, s i)`. The notation `⨂ₜ[R] i, f i` stands for `tprod R f`.

<?decl PiTensorProduct.tprod?>
:::

**Definition (Tensor power).** The $n$-th tensor power of an $R$-module $M$ is $M^{\otimes n} = \bigotimes_{i \in \{1, \dots, n\}} M$. Its pure tensors are written $x_1 \otimes \dots \otimes x_n$. By convention $M^{\otimes 0}$ is the product of the empty family.

::: mathlib
`TensorPower` · `Mathlib.LinearAlgebra.TensorPower.Basic`

An abbreviation for `⨂[R] (_ : Fin n), M`, with the notation `⨂[R]^n M`.

<?decl TensorPower?>
:::

**Definition (Direct sum).** Let $(A_i)_{i \in \iota}$ be a family of $R$-modules. The direct sum $\bigoplus_i A_i$ is the submodule of $\prod_i A_i$ of the families $(a_i)$ with $a_i = 0$ for all but finitely many $i$. The map $\operatorname{of}_j : A_j \to \bigoplus_i A_i$ puts $a$ in the place $j$.

::: mathlib
`DirectSum` · `Mathlib.Algebra.DirectSum.Basic`

The type `⨁ i, β i`, defined as the type `Π₀ i, β i` of functions with finite support. Most constructions need `[DecidableEq ι]`.

<?decl DirectSum?>
:::

::: mathlib
`DirectSum.lof` · `Mathlib.Algebra.DirectSum.Module`

The inclusion `lof R ι M i : M i →ₗ[R] ⨁ i, M i` as a linear map.

<?decl DirectSum.lof?>
:::

**Definition (Graded algebra).** Let $\iota$ be an additive monoid, for example $\mathbb{N}$ or $\mathbb{Z}/2$. An external graded algebra is a family $(A_i)_{i \in \iota}$ of $R$-modules with bilinear maps $A_i \times A_j \to A_{i+j}$ and a unit $1 \in A_0$, such that the multiplication is associative and unital. The direct sum $\bigoplus_i A_i$ is then an $R$-algebra. An internal grading of an $R$-algebra $A$ is a family of submodules $A_i \subseteq A$ with $1 \in A_0$, $A_i A_j \subseteq A_{i+j}$, and $A = \bigoplus_i A_i$, that is, each $a \in A$ is a unique finite sum $a = \sum_i a_i$ with $a_i \in A_i$.

An internal grading gives an external one, and the sum map $\bigoplus_i A_i \to A$ is then an isomorphism of algebras.

::: mathlib
`GradedMonoid.GMonoid` · `Mathlib.Algebra.GradedMonoid`

The external form: a family `A : ι → Type*` with `mul : A i → A j → A (i + j)`, a `one : A 0`, and the laws of a monoid. The laws are stated in the sigma type `GradedMonoid A`, since `(i + j) + k` and `i + (j + k)` are not equal by definition.

<?decl GradedMonoid.GMonoid?>
:::

::: mathlib
`SetLike.GradedMonoid` · `Mathlib.Algebra.GradedMonoid`

The internal form: a family `𝒜 : ι → S` of submodules (or subgroups) with `1 ∈ 𝒜 0` and `𝒜 i * 𝒜 j ⊆ 𝒜 (i + j)`.

<?decl SetLike.GradedMonoid?>
:::

::: mathlib
`DirectSum.Decomposition` · `Mathlib.Algebra.DirectSum.Decomposition`

The data of an inverse `decompose : M → ⨁ i, ℳ i` to the sum map.

<?decl DirectSum.Decomposition?>
:::

### Theorems and proofs

**Theorem (Universal property of the tensor product of a family).** Let $N$ be an $R$-module and $\varphi : \prod_i M_i \to N$ a multilinear map. There is a unique linear map $\bar\varphi : \bigotimes_i M_i \to N$ with $\bar\varphi(\bigotimes_i f_i) = \varphi(f)$ for all $f$.

*Proof.* By the universal property of the free module, there is a unique linear map $\Phi : F \to N$ with $\Phi[f] = \varphi(f)$. The map $\varphi$ is additive and homogeneous in each coordinate, so $\Phi$ sends each generator of $K$ to $0$. So $K \subseteq \ker \Phi$, and $\Phi$ factors through $F/K$ as a linear map $\bar\varphi$ with the stated values. The pure tensors span $F/K$, and this gives uniqueness. $\square$

::: mathlib
`PiTensorProduct.lift` · `Mathlib.LinearAlgebra.PiTensorProduct.Basic`

The bijection `MultilinearMap R s E ≃ₗ[R] ((⨂[R] i, s i) →ₗ[R] E)`. The value on a pure tensor is given by `PiTensorProduct.lift.tprod`.

<?decl PiTensorProduct.lift?>
:::

**Theorem (Basis of a tensor product).** Let $\iota$ be finite, and let each $M_i$ have a basis $(e^i_k)_{k \in \kappa_i}$. Then the pure tensors $e_k = \bigotimes_i e^i_{k_i}$, for $k \in \prod_i \kappa_i$, form a basis of $\bigotimes_i M_i$.

*Proof.* The pure tensors span. Write $f_i = \sum_k c^i_k e^i_k$ for each $i$. Multilinearity in each of the finitely many coordinates gives $\bigotimes_i f_i = \sum_{k} \bigl(\prod_i c^i_{k_i}\bigr) e_k$. So the $e_k$ span. For independence, let $(e^{i*}_k)$ be the coordinate functions of the bases. For a fixed $k$, the map $f \mapsto \prod_i e^{i*}_{k_i}(f_i)$ is multilinear into $R$. Let $\lambda_k$ be the linear form that the universal property gives. Then $\lambda_k(e_{k'}) = \prod_i \delta_{k_i k'_i} = \delta_{k k'}$. Apply $\lambda_k$ to a relation $\sum_{k'} a_{k'} e_{k'} = 0$. This gives $a_k = 0$ for each $k$. $\square$

When $M$ is free of rank $d$, the theorem gives $\operatorname{rank} M^{\otimes n} = d^n$.

::: mathlib
`Basis.piTensorProduct` · `Mathlib.LinearAlgebra.PiTensorProduct.Basis`

The basis of `⨂[R] i, M i` indexed by `Π i, κ i`, built from a family of bases. It needs `[Finite ι]`.

<?decl Basis.piTensorProduct?>
:::

**Theorem (Associativity of tensor powers).** For all $n, m$ there is a unique linear isomorphism $\mu : M^{\otimes n} \otimes M^{\otimes m} \to M^{\otimes (n+m)}$ with $\mu((x_1 \otimes \dots \otimes x_n) \otimes (y_1 \otimes \dots \otimes y_m)) = x_1 \otimes \dots \otimes x_n \otimes y_1 \otimes \dots \otimes y_m$.

*Proof.* The map $(x, y) \mapsto x_1 \otimes \dots \otimes y_m$ on $M^n \times M^m$ is multilinear in all $n + m$ coordinates. The universal property in $x$, then in $y$, then the universal property of $\otimes$ in Chapter 2, give $\mu$. For the inverse, the map $z \mapsto (z_1 \otimes \dots \otimes z_n) \otimes (z_{n+1} \otimes \dots \otimes z_{n+m})$ from $M^{n+m}$ is multilinear, so it gives a linear map $\nu$. The compositions $\mu \nu$ and $\nu \mu$ fix the pure tensors, which span. So they are the identities. $\square$

::: mathlib
`TensorPower.mulEquiv` · `Mathlib.LinearAlgebra.TensorPower.Basic`

The equivalence `⨂[R]^n M ⊗[R] ⨂[R]^m M ≃ₗ[R] ⨂[R]^(n + m) M`.

<?decl TensorPower.mulEquiv?>
:::

**Theorem (Universal property of the direct sum).** For linear maps $g_i : A_i \to N$ there is a unique linear map $g : \bigoplus_i A_i \to N$ with $g \circ \operatorname{of}_i = g_i$ for all $i$.

*Proof.* Each $a \in \bigoplus_i A_i$ is the finite sum $\sum_{i} \operatorname{of}_i(a_i)$ over the support of $a$. So $g$ must be $g(a) = \sum_i g_i(a_i)$. This sum is finite, and it is linear in $a$ because each $g_i$ is linear and the support of $a + b$ lies in the union of the supports. $\square$

::: mathlib
`DirectSum.toModule` · `Mathlib.Algebra.DirectSum.Module`

The map `toModule R ι N g : (⨁ i, M i) →ₗ[R] N`. The value on `lof R ι M i x` is `g i x` by `DirectSum.toModule_lof`.

<?decl DirectSum.toModule?>
:::

**Theorem (The tensor powers form a graded algebra).** The family $(M^{\otimes n})_{n \in \mathbb{N}}$, with the products $\mu$ and the unit $1 \in R = M^{\otimes 0}$, is an external graded algebra. So $\bigoplus_n M^{\otimes n}$ is an $R$-algebra with $(x_1 \otimes \dots \otimes x_n)(y_1 \otimes \dots \otimes y_m) = x_1 \otimes \dots \otimes x_n \otimes y_1 \otimes \dots \otimes y_m$.

*Proof.* The product on the direct sum is bilinear because $\mu$ is. Associativity is an equality of trilinear maps, so by the universal properties it is enough to check it on pure tensors. On pure tensors both sides are the concatenation of three lists of vectors. The unit law holds because $M^{\otimes 0} = R$ and $\mu(r \otimes x) = r x$. $\square$

### Examples

**Example (Dimensions of tensor powers).** Let $M = \mathbb{Q}^2$ with basis $e_1, e_2$. The basis of $M^{\otimes 3}$ has the $2^3 = 8$ elements $e_i \otimes e_j \otimes e_k$. The vector $t = e_1 \otimes e_2 \otimes e_1 - e_2 \otimes e_1 \otimes e_1$ is not a pure tensor. Suppose $t = x \otimes y \otimes z$. The coefficient of $e_i \otimes e_j \otimes e_k$ in $x \otimes y \otimes z$ is $x_i y_j z_k$. That of $e_1 \otimes e_2 \otimes e_1$ is $1$, so $x_1 \neq 0$ and $z_1 \neq 0$. That of $e_2 \otimes e_1 \otimes e_1$ is $-1$, so $y_1 \neq 0$. Then $x_1 y_1 z_1 \neq 0$, but the coefficient of $e_1 \otimes e_1 \otimes e_1$ in $t$ is $0$.

**Example (A $\mathbb{Z}/2$-grading).** On $\mathbb{C}$ as an $\mathbb{R}$-algebra let $A_0 = \mathbb{R}$ and $A_1 = \mathbb{R} i$. Then $A_1 A_1 = \mathbb{R} i^2 = A_0$, which is the rule $1 + 1 = 0$ in $\mathbb{Z}/2$. The same algebra has no $\mathbb{N}$-grading with $i$ of degree $1$, since $i^2 = -1$ would have to lie in $A_2$ and in $A_0$, and $A_0 \cap A_2 = 0$.

**Counterexample (A basis needs free factors).** Over $\mathbb{Z}$, let $M_1 = \mathbb{Z}/2$ and $M_2 = \mathbb{Z}/3$. Then $M_1 \otimes M_2 = 0$. Indeed, $x \otimes y = 3 (x \otimes y) - 2 (x \otimes y) = x \otimes (3y) - (2x) \otimes y = 0 - 0$. So the basis theorem fails for factors that are not free.

### The library around it

The instances `TensorPower.gmonoid` and `TensorPower.galgebra` make the tensor powers a graded algebra. Internal gradings, with `GradedAlgebra`, are in `Mathlib.RingTheory.GradedAlgebra.Basic`. A direct sum of free modules is free by the instance `Module.Free.directSum`, and a direct sum of finitely many finite modules is finite by `Module.Finite.instDirectSum`, with the same result `Module.Finite.instDFinsupp` for the type `Π₀ i, M i`.

### Exercises

1. (A) Find a basis of $(\mathbb{Q}^3)^{\otimes 2}$ and write $(e_1 + 2 e_3) \otimes (e_2 - e_3)$ in it. Hint: expand by bilinearity.
2. (A) Show that $M^{\otimes 1} \cong M$ and $M^{\otimes 0} \cong R$. Hint: for $n = 0$, a multilinear map on the empty family is a constant.
3. (B) Let $A = \bigoplus_i A_i$ be an internal grading by $\mathbb{N}$. Show that $A_0$ is a subalgebra and that $A_+ = \bigoplus_{i > 0} A_i$ is a two-sided ideal. Hint: use $A_i A_j \subseteq A_{i+j}$.
4. (B) Let $M$ be free with basis $e_1, \dots, e_d$. Show that $x \in M^{\otimes 2}$ is a pure tensor exactly when its matrix of coefficients $(c_{ij})$ has rank at most $1$ over a field. Hint: $x \otimes y$ has the matrix $x y^{\mathsf{T}}$.
5. (B) Show that $\bigoplus_n M^{\otimes n}$ is not commutative when $M$ is free of rank at least $2$. Hint: compare $e_1 \otimes e_2$ and $e_2 \otimes e_1$.
6. (C) Let $A$ be an internal $\mathbb{Z}$-grading of a commutative ring with no zero divisors. Show that a unit of $A$ is homogeneous. Hint: compare the highest and the lowest nonzero components of $u$ and $u^{-1}$.

### Notes and history

Tensors entered geometry with the absolute differential calculus of Ricci and Levi-Civita, published in 1900.

Mathlib uses one definition for the tensor product of any family. The binary tensor product of Chapter 2 is a separate definition, and `PiTensorProduct.tmulEquiv` connects the two.

### Reference

<?reference?>
