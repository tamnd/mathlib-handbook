---
title: Bilinear maps
kind: theory
modules:
  - Mathlib.LinearAlgebra.BilinearMap
explains:
  E3: [LinearMap.mk₂, LinearMap.flip]
  E2: [LinearMap.map_add₂, LinearMap.map_smul₂, LinearMap.map_zero₂, LinearMap.ext₂, LinearMap.flip_flip, LinearMap.lflip, LinearMap.compl₁₂, LinearMap.compl₂, LinearMap.compr₂, LinearMap.lcomp, LinearMap.llcomp, LinearMap.lsmul, IsBilinearMap]
  E1: auto
families: []
requires: [V07.C01, V07.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Bilinear maps

### Overview

The product in a ring, the dot product, the value $\varphi(v)$ of a linear form at a vector and the composition $g \circ f$ of linear maps all take two arguments. None of them is linear as a function of the pair, but each is linear in each argument when the other is fixed. Such an operation is a bilinear map.

This section identifies a bilinear map $M \times N \to P$ with a linear map $M \to \operatorname{Hom}_R(N, P)$, the form that Mathlib uses. It proves that a bilinear form on $R^m \times R^n$ is $x^{\mathsf{T}} A y$ for a unique matrix $A$, and it studies the flip and compositions. It uses Volume 7, Chapters 1 and 2.

### Definitions

Fix a commutative ring $R$ and $R$-modules $M$, $N$ and $P$.

**Definition (Bilinear map).** A function $f : M \times N \to P$ is bilinear if for all $m, m' \in M$, $n, n' \in N$ and $c \in R$:
$$f(m + m', n) = f(m, n) + f(m', n), \quad f(c m, n) = c f(m, n), \quad f(m, n + n') = f(m, n) + f(m, n'), \quad f(m, c n) = c f(m, n).$$

So $f$ is linear in each argument when the other is fixed. A bilinear map with values in $R$ is a bilinear form; Chapter 5 studies them. The bilinear maps $M \times N \to P$ form an $R$-module under the pointwise operations. For the scalar multiple, $(a f)(c m, n) = a c f(m, n) = c (a f)(m, n)$, and this step uses $a c = c a$.

**Definition (Curried form).** For a bilinear map $f$, let $\tilde f : M \to \operatorname{Hom}_R(N, P)$ be the map $\tilde f(m) = f(m, \cdot)$, so $\tilde f(m)(n) = f(m, n)$.

Linearity in $n$ says that $\tilde f(m)$ is linear, and linearity in $m$ says that $\tilde f$ is linear. Here $\operatorname{Hom}_R(N, P)$ is an $R$-module because $R$ is commutative (Volume 7, Chapter 1).

::: mathlib
`LinearMap.mk₂` · `Mathlib.LinearAlgebra.BilinearMap`

A bilinear map is a term of `M →ₗ[R] N →ₗ[R] P`, the curried form. The constructor `LinearMap.mk₂ R f H1 H2 H3 H4` takes a function `f : M → N → P` and the four rules of the definition, and returns the curried linear map.

<?decl LinearMap.mk₂?>
:::

### Theorems and proofs

**Proposition (Bilinear maps are curried linear maps).** The map $f \mapsto \tilde f$ is an isomorphism of $R$-modules from the module of the bilinear maps $M \times N \to P$ to $\operatorname{Hom}_R(M, \operatorname{Hom}_R(N, P))$.

*Proof.* The map $f \mapsto \tilde f$ respects sums and scalar multiples, since both sides are computed pointwise. It is injective, since $\tilde f = 0$ means $f(m, n) = \tilde f(m)(n) = 0$ for all $m, n$. For the surjectivity, take a linear map $F : M \to \operatorname{Hom}_R(N, P)$ and put $f(m, n) = F(m)(n)$. For fixed $m$, $n \mapsto F(m)(n)$ is linear. For fixed $n$, $f(m + m', n) = F(m + m')(n) = (F(m) + F(m'))(n) = f(m, n) + f(m', n)$, and the same computation works for $c m$. So $f$ is bilinear, and $\tilde f = F$. $\square$

Since $f(\cdot, n)$ and $f(m, \cdot)$ are linear, $f(0, n) = f(m, 0) = 0$, and an expansion in one argument at a time gives $f(\sum_i a_i m_i, \sum_j b_j n_j) = \sum_{i, j} a_i b_j f(m_i, n_j)$.

::: mathlib
`LinearMap.map_add₂` · `Mathlib.LinearAlgebra.BilinearMap`

Additivity in the first argument: `f (x₁ + x₂) y = f x₁ y + f x₂ y`. In the second argument `f x` is a linear map, so `map_add (f x)` applies; the curried form makes the two arguments asymmetric.

<?decl LinearMap.map_add₂?>
:::

**Theorem (A bilinear map is determined on generators).** Let $S \subseteq M$ and $T \subseteq N$ span $M$ and $N$. If two bilinear maps $f, g : M \times N \to P$ agree on $S \times T$, then $f = g$.

*Proof.* The map $f - g$ is bilinear and vanishes on $S \times T$. Fix $t \in T$. The linear map $(f - g)(\cdot, t)$ vanishes on $S$, so it vanishes on the span of $S$, which is $M$. Now fix $m \in M$. The linear map $(f - g)(m, \cdot)$ vanishes on $T$, by the first step, so it vanishes on $N$. $\square$

::: mathlib
`LinearMap.ext₂` · `Mathlib.LinearAlgebra.BilinearMap`

If `f m n = g m n` for all `m` and `n`, then `f = g`. The version for spanning sets follows by two applications of `LinearMap.ext_on`. The companions `LinearMap.map_smul₂` and `LinearMap.map_zero₂` give `f (r • x) y = r • f x y` and `f 0 y = 0`.

<?decl LinearMap.ext₂?>
:::

**Theorem (Bilinear maps on free modules).** Let $M$ and $N$ be free with bases $(e_i)_{i \in I}$ and $(f_j)_{j \in J}$. For each family $(p_{ij})$ of elements of $P$ there is exactly one bilinear map $\beta$ with $\beta(e_i, f_j) = p_{ij}$ for all $i, j$.

*Proof.* Uniqueness is the previous theorem. For existence, fix $i$. A linear map on a free module may take arbitrary values on a basis (Volume 7, Chapter 2), so there is a linear map $g_i : N \to P$ with $g_i(f_j) = p_{ij}$. Again there is a linear map $F : M \to \operatorname{Hom}_R(N, P)$ with $F(e_i) = g_i$. The bilinear map that corresponds to $F$ is $\beta(m, n) = F(m)(n)$, and $\beta(e_i, f_j) = g_i(f_j) = p_{ij}$. $\square$

**Corollary (Matrices of bilinear forms).** Each bilinear form $\beta : R^m \times R^n \to R$ has the form $\beta(x, y) = x^{\mathsf{T}} A y = \sum_{i, j} x_i A_{ij} y_j$ for exactly one $m \times n$ matrix $A$, namely $A_{ij} = \beta(e_i, e_j)$. Over a field $K$, the bilinear forms on $K^m \times K^n$ form a space of dimension $m n$.

*Proof.* The function $x^{\mathsf{T}} A y$ is bilinear with value $A_{ij}$ at $(e_i, e_j)$, so the theorem applies. The map $\beta \mapsto (\beta(e_i, e_j))$ is linear and bijective onto the space of $m \times n$ matrices, which has dimension $m n$. $\square$

### Operations on bilinear maps

**Definition (Flip).** The flip of a bilinear map $f : M \times N \to P$ is the bilinear map $f^{\mathrm{flip}} : N \times M \to P$, $f^{\mathrm{flip}}(n, m) = f(m, n)$.

The flip of the flip is $f$, and $f \mapsto f^{\mathrm{flip}}$ is linear, so it is an isomorphism of modules. For a form on $R^m \times R^n$ the flip replaces $A$ by $A^{\mathsf{T}}$, since $y^{\mathsf{T}} A^{\mathsf{T}} x = x^{\mathsf{T}} A y$.

::: mathlib
`LinearMap.flip` · `Mathlib.LinearAlgebra.BilinearMap`

The exchange of the arguments: `f.flip n m = f m n`. The lemma `LinearMap.flip_flip` states `f.flip.flip = f`, and `LinearMap.lflip` is the flip as a linear equivalence.

<?decl LinearMap.flip?>
:::

**Definition (Composition with linear maps).** Let $f : M \times N \to P$ be bilinear. For linear maps $g : Q \to M$, $h : Q' \to N$ and $k : P \to P'$, the functions
$$(q, q') \mapsto f(g(q), h(q')), \qquad (m, n) \mapsto k(f(m, n))$$
are bilinear maps $Q \times Q' \to P$ and $M \times N \to P'$.

In each argument this is a composition of linear maps.

::: mathlib
`LinearMap.compl₁₂` · `Mathlib.LinearAlgebra.BilinearMap`

The map with `f.compl₁₂ g g' q q' = f (g q) (g' q')`; `f.compl₂ g'` acts on the second argument only. On the other side, `f.compr₂ k m n = k (f m n)`. For a form `B`, `B.compl₁₂ g g` is the pullback $B(g x, g y)$ of Chapter 5.

<?decl LinearMap.compl₁₂?>
<?decl LinearMap.compr₂?>
:::

The composition $(v, u) \mapsto v \circ u$ is a bilinear map $\operatorname{Hom}(N, P) \times \operatorname{Hom}(M, N) \to \operatorname{Hom}(M, P)$: $(v + v') \circ u = v \circ u + v' \circ u$, and $v \circ (u + u') = v \circ u + v \circ u'$ because $v$ is linear.

::: mathlib
`LinearMap.llcomp` · `Mathlib.LinearAlgebra.BilinearMap`

The composition as a bilinear map, with the outer map as the first argument: `LinearMap.llcomp R M N P v u = v ∘ₗ u`. For a fixed `u`, `LinearMap.lcomp` is $v \mapsto v \circ u$.

<?decl LinearMap.llcomp?>
:::

### Examples

**Example (The matrix of a form).** On $\mathbb{Q}^2 \times \mathbb{Q}^3$ let $\beta(x, y) = x_1 y_1 + 2 x_1 y_3 - x_2 y_2 + 5 x_2 y_3$. The values on the standard bases are $\beta(e_1, e_1) = 1$, $\beta(e_1, e_3) = 2$, $\beta(e_2, e_2) = -1$, $\beta(e_2, e_3) = 5$ and $0$ for the other two pairs. So
$$A = \begin{pmatrix} 1 & 0 & 2 \\ 0 & -1 & 5 \end{pmatrix}, \qquad \beta(x, y) = x^{\mathsf{T}} A y.$$
For $x = (1, 2)$ and $y = (3, 1, -1)$: $A y = (3 - 2, -1 - 5) = (1, -6)$, and $x^{\mathsf{T}} A y = 1 - 12 = -11$. The flip has the matrix $A^{\mathsf{T}}$ of size $3 \times 2$.

**Counterexample (A bilinear map is not linear).** The multiplication $\mu(x, y) = x y$ on $\mathbb{R} \times \mathbb{R}$ is bilinear but not linear on the module $\mathbb{R} \times \mathbb{R}$: $\mu(2, 2) = 4$, but $\mu(1, 1) + \mu(1, 1) = 2$. In general $f(c m, c n) = c^2 f(m, n)$. Chapter 2 builds the tensor product, a module on which bilinear maps become linear.

**Counterexample (Commutativity of the ring is needed).** On the quaternions $\mathbb{H}$, a left module over itself, the multiplication $(a, b) \mapsto a b$ is additive in both arguments and $(c a) b = c (a b)$. But for $a = i$, $b = 1$, $c = j$: $a (c b) = i j = k$ and $c (a b) = j i = -k$. So the multiplication is not bilinear.

### The library around it

The file states these operations in a semilinear generality, for the sesquilinear forms of Chapter 5. The scalar multiplication $R \times M \to M$ is the bilinear map `LinearMap.lsmul R M`. The structure `IsBilinearMap` states the four rules for a plain function `E → F → G`.

### Exercises

1. (A) Show that the cross product $\mathbb{R}^3 \times \mathbb{R}^3 \to \mathbb{R}^3$ is bilinear. Hint: each coordinate is a sum of terms $\pm x_i y_j$.
2. (A) Find the matrix of the form $\beta(x, y) = (x_1 + x_2)(y_1 - y_2)$ on $\mathbb{Q}^2 \times \mathbb{Q}^2$, and of its flip. Hint: compute the four values $\beta(e_i, e_j)$.
3. (A) Let $f$ be bilinear. Show that $f(m + m', n + n') = f(m, n) + f(m, n') + f(m', n) + f(m', n')$. Hint: expand in one argument at a time.
4. (B) Let $\beta$ be a bilinear form on $R^n \times R^n$ with matrix $A$, and let $g$ be an endomorphism of $R^n$ with matrix $G$. Show that $\beta(g x, g y)$ has the matrix $G^{\mathsf{T}} A G$. Hint: $(G x)^{\mathsf{T}} = x^{\mathsf{T}} G^{\mathsf{T}}$.
5. (B) Show that a function $f : \mathbb{Z} \times \mathbb{Z} \to \mathbb{Z}$ that is additive in each argument is $\mathbb{Z}$-bilinear, and that it equals $f(1, 1) x y$. Hint: induction on $c \in \mathbb{N}$.
6. (B) Over a field $K$, let $\beta : V \times W \to K$ be bilinear, with $V$ and $W$ of finite dimension. Show that the rank of the curried map $V \to W^*$ equals the rank of the flipped map $W \to V^*$. Hint: the matrices are $A$ and $A^{\mathsf{T}}$.
7. (C) Let $f : M \times N \to P$ be bilinear and let $f(m, n) = 0$ whenever $m \in M'$ for a submodule $M' \subseteq M$. Show that $f$ induces a bilinear map $M / M' \times N \to P$. Hint: the curried map vanishes on $M'$.

### Notes and history

Bilinear forms appeared first in number theory, as the quadratic forms of Lagrange and Gauss, long before the general notion of a module.

### Reference

<?reference?>
