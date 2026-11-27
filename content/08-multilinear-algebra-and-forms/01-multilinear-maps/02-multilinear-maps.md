---
title: Multilinear maps
kind: theory
modules:
  - Mathlib.LinearAlgebra.Multilinear.Basic
  - Mathlib.LinearAlgebra.Multilinear.Curry
  - Mathlib.LinearAlgebra.Multilinear.Basis
  - Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
  - Mathlib.LinearAlgebra.Multilinear.Pi
explains:
  E3: [MultilinearMap, MultilinearMap.map_sum, Module.Basis.ext_multilinear]
  E2: [MultilinearMap.map_update_add, MultilinearMap.map_update_smul, MultilinearMap.map_coord_zero, MultilinearMap.map_smul_univ, MultilinearMap.mkPiRing, MultilinearMap.piRingEquiv, MultilinearMap.curryLeft, multilinearCurryLeftEquiv, MultilinearMap.compLinearMap, MultilinearMap.domDomCongr, Basis.multilinearMap, Module.Free.multilinearMap, Module.Finite.multilinearMap, MultilinearMap.pi_ext]
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

## Multilinear maps

### Overview

The determinant of a matrix is linear in each column when the other columns are fixed. The product $x_1 \cdots x_n$ and the triple product $u \cdot (v \times w)$ have the same property. A function of $n$ arguments that is linear in each argument separately is a multilinear map. For $n = 2$ it is a bilinear map of Section 1 of this chapter.

This section proves the basic rules, the expansion of sums, the description on free modules, and currying. Section 3 uses these results.

### Definitions

Fix a commutative ring $R$, a finite set $\iota$, modules $M_i$ for $i \in \iota$ and a module $N$. For $i \in \iota$ and $x \in M_i$, write $m[i \mapsto x]$ for the tuple that has $x$ at the place $i$ and $m_j$ at each place $j \neq i$.

**Definition (Multilinear map).** A function $f : \prod_{i \in \iota} M_i \to N$ is multilinear if for each tuple $m$, each $i \in \iota$, all $x, y \in M_i$ and all $c \in R$:
$$f(m[i \mapsto x + y]) = f(m[i \mapsto x]) + f(m[i \mapsto y]), \qquad f(m[i \mapsto c x]) = c \, f(m[i \mapsto x]).$$

So $x \mapsto f(m[i \mapsto x])$ is linear for each place $i$. The multilinear maps form an $R$-module $\operatorname{Mult}_R(M_1, \dots, M_n; N)$ under the pointwise operations; as in Section 1, the scalar multiple is multilinear because $R$ is commutative.

::: mathlib
`MultilinearMap` · `Mathlib.LinearAlgebra.Multilinear.Basic`

A structure with a function `toFun : (∀ i, M i) → N` and two fields, `map_update_add'` and `map_update_smul'`, which are the two rules of the definition stated with `Function.update m i x`. The notation is `(Π i, M i) →ₘₗ[R] N`. The lemmas `MultilinearMap.map_update_add` and `MultilinearMap.map_update_smul` give the two rules.

<?decl MultilinearMap?>
:::

### Theorems and proofs

**Proposition (A zero argument).** If $m_i = 0$ for some $i$, then $f(m) = 0$.

*Proof.* Put $x = 0$ in the second rule with $c = 0$: $f(m[i \mapsto 0]) = f(m[i \mapsto 0 \cdot 0]) = 0 \cdot f(m[i \mapsto 0]) = 0$. Since $m_i = 0$, $m[i \mapsto 0] = m$. $\square$

In Mathlib this is `MultilinearMap.map_coord_zero`.

**Proposition (Scalars in all arguments).** For scalars $(c_i)_{i \in \iota}$ and a tuple $m$, $f((c_i m_i)_i) = \big(\prod_i c_i\big) f(m)$. In particular $f(c m) = c^{|\iota|} f(m)$.

*Proof.* Order $\iota$ as $1, \dots, n$ and let $m^{(k)}$ be the tuple with $c_i m_i$ at the places $i \le k$ and $m_i$ at the places $i > k$. Then $m^{(k)} = m^{(k-1)}[k \mapsto c_k m_k]$, so the second rule gives $f(m^{(k)}) = c_k f(m^{(k-1)})$. By induction $f(m^{(n)}) = c_n \cdots c_1 f(m^{(0)})$, and $m^{(0)} = m$. $\square$

::: mathlib
`MultilinearMap.map_smul_univ` · `Mathlib.LinearAlgebra.Multilinear.Basic`

The formula `f (fun i => c i • m i) = (∏ i, σ (c i)) • f m` for a finite index type.

<?decl MultilinearMap.map_smul_univ?>
:::

**Theorem (Expansion of sums).** For each $i \in \iota$ let $J_i$ be a finite set and $g_i : J_i \to M_i$ a function. Then
$$f\Big(\Big(\sum_{j \in J_i} g_i(j)\Big)_{i \in \iota}\Big) = \sum_{r \in \prod_i J_i} f\big((g_i(r_i))_{i \in \iota}\big),$$
where $r$ runs over all the choice functions, which pick one $r_i \in J_i$ for each $i$.

*Proof.* At one place, the linear map $x \mapsto f(m[i \mapsto x])$ sends a finite sum $\sum_{j \in J} g(j)$ to $\sum_{j \in J} f(m[i \mapsto g(j)])$; for $J = \emptyset$ both sides are $0$. Now order $\iota$ as $1, \dots, n$ and write $s_i = \sum_{j \in J_i} g_i(j)$. For $0 \le k \le n$ let $P_k$ be the claim
$$f(s_1, \dots, s_n) = \sum_{r_1 \in J_1, \dots, r_k \in J_k} f(g_1(r_1), \dots, g_k(r_k), s_{k+1}, \dots, s_n).$$
The claim $P_0$ is trivial. To pass from $P_k$ to $P_{k+1}$, expand each term at the place $k + 1$ by the case of one place. The claim $P_n$ is the theorem. $\square$

::: mathlib
`MultilinearMap.map_sum` · `Mathlib.LinearAlgebra.Multilinear.Basic`

The expansion `f (fun i => ∑ j, g i j) = ∑ r : ∀ i, α i, f (fun i => g i (r i))`, with finite types `α i`. The form `MultilinearMap.map_sum_finset` takes a `Finset` for each place.

<?decl MultilinearMap.map_sum?>
:::

**Theorem (Multilinear maps on free modules).** Let each $M_i$ be free with a finite basis $(e_{i, j})_{j \in J_i}$. For $r \in \prod_i J_i$ write $e_r = (e_{i, r_i})_{i \in \iota}$. For each family $(p_r)_{r \in \prod_i J_i}$ of elements of $N$ there is exactly one multilinear map $f$ with $f(e_r) = p_r$ for all $r$.

*Proof.* Let $x_{i, j} : M_i \to R$ be the coordinate functions of the basis, so $m_i = \sum_j x_{i, j}(m_i) e_{i, j}$. Uniqueness: the expansion theorem with $g_i(j) = x_{i, j}(m_i) e_{i, j}$ and then the scalar rule give
$$f(m) = \sum_{r} \Big(\prod_{i} x_{i, r_i}(m_i)\Big) f(e_r) = \sum_r \Big(\prod_i x_{i, r_i}(m_i)\Big) p_r.$$
Call this formula $(*)$. Existence: define $f$ by the right side of $(*)$. For a fixed $r$ and a fixed place $k$, the scalar $\prod_i x_{i, r_i}(m_i)$ is the linear function $x_{k, r_k}(m_k)$ of $m_k$ times a product that does not depend on $m_k$. Since $R$ is commutative, this is linear in $m_k$. So each term of $(*)$ is multilinear, and a finite sum of multilinear maps is multilinear. At $m = e_s$, $x_{i, r_i}(e_{i, s_i})$ is $1$ for $r_i = s_i$ and $0$ otherwise, so the product is $1$ for $r = s$ and $0$ for $r \neq s$. Thus $f(e_s) = p_s$. $\square$

::: mathlib
`Module.Basis.ext_multilinear` · `Mathlib.LinearAlgebra.Multilinear.Basis`

The uniqueness half: for bases `e i` of the modules `M i` and a finite index type, two multilinear maps that agree on all tuples `fun i => e i (v i)` are equal.

<?decl Module.Basis.ext_multilinear?>
:::

**Corollary (Dimension).** Let $K$ be a field and $V_1, \dots, V_n, W$ vector spaces of finite dimension. Then
$$\dim_K \operatorname{Mult}_K(V_1, \dots, V_n; W) = \dim V_1 \cdots \dim V_n \cdot \dim W.$$

*Proof.* Choose bases. By the theorem, the map $f \mapsto (f(e_r))_r$ is a bijection from the multilinear maps to $W^{\prod_i J_i}$, and it is linear. The space $W^{\prod_i J_i}$ has dimension $|J_1| \cdots |J_n| \cdot \dim W$. $\square$

::: mathlib
`Basis.multilinearMap` · `Mathlib.LinearAlgebra.Multilinear.Basis`

From bases `b i` of the modules `M i` and a basis `b'` of `N`, a basis of `(Π i, M i) →ₘₗ[R] N` indexed by `(Π i, κ i) × ι'`. The instances `Module.Free.multilinearMap` and `Module.Finite.multilinearMap` say that the module of multilinear maps between finite free modules is finite and free.

<?decl Basis.multilinearMap?>
:::

### Multilinear maps on $R^n$ and currying

Take every $M_i = R$. A tuple is then a vector $m \in R^\iota$.

**Proposition (Multilinear maps on $R^\iota$).** The map $f \mapsto f(1, \dots, 1)$ is an isomorphism of modules $\operatorname{Mult}_R(R, \dots, R; N) \to N$. Its inverse sends $z$ to the map $m \mapsto (\prod_i m_i) z$.

*Proof.* The map $m \mapsto (\prod_i m_i) z$ is multilinear, since $\prod_i m_i$ is linear in each $m_k$ when the others are fixed. Its value at $(1, \dots, 1)$ is $z$. Conversely, by the scalar rule $f(m) = f((m_i \cdot 1)_i) = (\prod_i m_i) f(1, \dots, 1)$. So the two maps are inverse, and $f \mapsto f(1, \dots, 1)$ is linear. $\square$

::: mathlib
`MultilinearMap.mkPiRing` · `Mathlib.LinearAlgebra.Multilinear.Basic`

The map `MultilinearMap.mkPiRing R ι z` on `ι → R` with the value `(∏ i, m i) • z`. The linear equivalence `MultilinearMap.piRingEquiv : N ≃ₗ[R] (ι → R) →ₘₗ[R] N` packs the proposition.

<?decl MultilinearMap.mkPiRing?>
<?decl MultilinearMap.piRingEquiv?>
:::

**Theorem (Currying).** Let $\iota = \{0, 1, \dots, n\}$. The map that sends $f$ to $x \mapsto f(x, \cdot)$ is an isomorphism of modules
$$\operatorname{Mult}_R(M_0, M_1, \dots, M_n; N) \cong \operatorname{Hom}_R\big(M_0, \operatorname{Mult}_R(M_1, \dots, M_n; N)\big).$$

*Proof.* For a fixed $x \in M_0$, the map $(m_1, \dots, m_n) \mapsto f(x, m_1, \dots, m_n)$ is multilinear by the rules at the places $1, \dots, n$, and it is linear in $x$ by the rules at the place $0$. The map is linear and injective, as in Section 1. Conversely, for a linear $F$ put $f(x, m_1, \dots, m_n) = F(x)(m_1, \dots, m_n)$. The rules at the places $1, \dots, n$ hold because $F(x)$ is multilinear, and at the place $0$ because $F$ is linear and the operations are pointwise. $\square$

For $n = 2$ this is the curried form of Section 1.

::: mathlib
`MultilinearMap.curryLeft` · `Mathlib.LinearAlgebra.Multilinear.Curry`

For `f` on a family indexed by `Fin (n + 1)`, `f.curryLeft x` is the map `m ↦ f (Fin.cons x m)` on the remaining `n` arguments. The inverse is `LinearMap.uncurryLeft`, and `multilinearCurryLeftEquiv` packs both as a linear equivalence.

<?decl MultilinearMap.curryLeft?>
<?decl multilinearCurryLeftEquiv?>
:::

For linear maps $g_i : M'_i \to M_i$, the map $m \mapsto f((g_i(m_i))_i)$ is multilinear; it is `f.compLinearMap g`. For a bijection $e$ of the index sets, $v \mapsto f(v \circ e)$ is `MultilinearMap.domDomCongr e f`; Section 3 uses it to permute the arguments. The lemma `MultilinearMap.pi_ext` is the uniqueness theorem for the modules $R^{J_i}$.

### Examples

**Example (Trilinear forms on $\mathbb{Q}^2$).** The trilinear forms on $\mathbb{Q}^2 \times \mathbb{Q}^2 \times \mathbb{Q}^2$ form a space of dimension $2^3 = 8$, with the basis $x_a y_b z_c$ for $a, b, c \in \{1, 2\}$. Take $f(x, y, z) = x_1 y_2 z_1 - x_2 y_2 z_2$. Then $p_{(1,2,1)} = 1$, $p_{(2,2,2)} = -1$, and the other six values on the basis are $0$. For $x = (1, 2)$, $y = (3, 1)$ and $z = (1, -1)$ the formula $(*)$ gives $1 \cdot 1 \cdot 1 - 2 \cdot 1 \cdot (-1) = 3$.

**Counterexample (A multilinear map is not linear).** The product $f(m) = m_1 m_2 m_3$ on $\mathbb{Q}^3$ is `MultilinearMap.mkPiRing ℚ (Fin 3) 1`. It is not linear on the module $\mathbb{Q}^3$: $f(2, 2, 2) = 8$, while $2 f(1, 1, 1) = 2$. This is the rule $f(c m) = c^3 f(m)$.

**Counterexample (The dimension formula needs free modules).** Over $\mathbb{Z}$ take $M_1 = \mathbb{Z}/2$ and $M_2 = \mathbb{Z}/3$, and let $f : M_1 \times M_2 \to N$ be bilinear for any $N$. Then $2 f(x, y) = f(2 x, y) = f(0, y) = 0$ and $3 f(x, y) = f(x, 3 y) = 0$, so $f(x, y) = 3 f(x, y) - 2 f(x, y) = 0$. So each bilinear map is zero, and the corollary fails for these modules, which are not free. Chapter 2 restates this fact as $\mathbb{Z}/2 \otimes \mathbb{Z}/3 = 0$.

### The library around it

The file `Basic` also has `MultilinearMap.mkPiAlgebra`, which multiplies the arguments in an algebra, and `Curry` has `MultilinearMap.curryRight`. The link with tensor products is in Chapter 3.

### Exercises

1. (A) Show that $f(x, y, z) = x \cdot (y \times z)$ on $\mathbb{R}^3$ is trilinear, and find its values $f(e_a, e_b, e_c)$. Hint: a determinant.
2. (A) Let $f$ be multilinear with $n$ arguments. Compute $f(-m)$ in terms of $f(m)$. Hint: the scalar rule with $c = -1$.
3. (A) Show that $f(m_1 + m_1', m_2 + m_2', m_3)$ is a sum of four values of $f$. Hint: the expansion theorem.
4. (B) Show that the composition $(u_1, \dots, u_n) \mapsto u_n \circ \dots \circ u_1$ of linear maps $u_k : M_{k-1} \to M_k$ is multilinear. Hint: fix all but one map.
5. (B) Over a field $K$, compute the dimension of the space of multilinear maps $K^2 \times K^3 \times K^4 \to K^5$. Hint: the corollary.
6. (B) Show that a multilinear map $f$ on $R^\iota$ with $f(1, \dots, 1) = 0$ is zero. Hint: the proposition on $R^\iota$.
7. (C) Let $M_1 = \mathbb{Z}/a$ and $M_2 = \mathbb{Z}/b$ over $\mathbb{Z}$. Show that each bilinear map $f$ on $M_1 \times M_2$ satisfies $d f = 0$ for $d = \gcd(a, b)$. Hint: write $d = u a + v b$.

### Notes and history

The determinant was the first multilinear function studied in detail.

### Reference

<?reference?>
