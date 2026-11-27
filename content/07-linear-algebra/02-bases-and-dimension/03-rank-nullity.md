---
title: Finite dimension and the rank-nullity theorem
kind: theory
modules:
  - Mathlib.LinearAlgebra.Dimension.Finrank
  - Mathlib.LinearAlgebra.Dimension.RankNullity
  - Mathlib.LinearAlgebra.FiniteDimensional.Defs
  - Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
  - Mathlib.LinearAlgebra.FiniteDimensional.Basic
  - Mathlib.LinearAlgebra.Dimension.Constructions
explains:
  E3: [Module.finrank, LinearMap.finrank_range_add_finrank_ker, LinearMap.rank_range_add_rank_ker]
  E2: [FiniteDimensional, HasRankNullity, Module.finrank_eq_card_basis, Submodule.finrank_quotient_add_finrank, Submodule.finrank_sup_add_finrank_inf_eq, LinearMap.injective_iff_surjective, Submodule.finrank_le, FiniteDimensional.nonempty_linearEquiv_of_finrank_eq]
  E1: auto
families: []
requires: [V07.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Finite dimension and the rank-nullity theorem

### Overview

A linear map $f : V \to W$ loses some information and keeps the rest. The kernel holds what it loses, and the range holds what it keeps. The rank-nullity theorem makes this exact for a space $V$ of finite dimension:
$$\dim \operatorname{im} f + \dim \ker f = \dim V.$$
A system of $m$ linear equations in $n$ unknowns is a map $K^n \to K^m$. The theorem says that its solutions form a space of dimension $n - r$, where $r$ is the dimension of the range. So $n - r$ unknowns can be chosen freely. In particular a system with fewer equations than unknowns always has a nonzero solution.

This section introduces `Module.finrank`, the dimension as a natural number, and proves the theorem in three forms: for a map, for a quotient, and for the sum of two subspaces. The corollaries include the fact that an endomorphism of a space of finite dimension is injective if and only if it is surjective, and that two spaces of the same finite dimension are isomorphic.

### Definitions

**Definition (Finite dimension).** A vector space $V$ is finite dimensional if it is spanned by a finite set. Its dimension $\dim_K V$ is then the number of vectors of a basis, a natural number.

A finite spanning set contains a basis by Section 2, and this basis is finite. All the bases have the same number of vectors, so $\dim_K V$ is well defined.

::: mathlib
`Module.finrank` · `Mathlib.LinearAlgebra.Dimension.Finrank`

The dimension as a natural number: `Module.finrank R M = Cardinal.toNat (Module.rank R M)`. The function `Cardinal.toNat` sends each infinite cardinal to `0`. So `finrank` is the dimension when it is finite, and it is `0` for a space of infinite dimension. A theorem on `finrank` that is not trivial in the infinite case carries a hypothesis such as `[FiniteDimensional K V]`. This convention avoids the type `ℕ∞` and keeps the arithmetic in `ℕ`.

<?decl Module.finrank?>
:::

::: mathlib
`FiniteDimensional` · `Mathlib.LinearAlgebra.FiniteDimensional.Defs`

The class `FiniteDimensional K V` for a vector space over a division ring. It is an abbreviation of `Module.Finite K V`, the statement that the module is finitely generated. Instances give it for `Fin n → K`, for products, for subspaces and for quotients of a finite dimensional space.

<?decl FiniteDimensional?>
:::

::: mathlib
`Module.finrank_eq_card_basis` · `Mathlib.LinearAlgebra.Dimension.StrongRankCondition`

For a basis indexed by a finite type: `finrank R M = Fintype.card ι`. It holds over each ring with the strong rank condition. This is the usual way to compute a dimension: exhibit a basis and count it.

<?decl Module.finrank_eq_card_basis?>
:::

### Theorems and proofs

In this part $K$ is a field, and $V$ and $W$ are vector spaces over $K$.

**Theorem (Subspaces).** Let $V$ be finite dimensional and $U$ a subspace. Then $U$ is finite dimensional and $\dim U \le \dim V$. If $\dim U = \dim V$, then $U = V$.

*Proof.* An independent family in $U$ is independent in $V$, so it has at most $n = \dim V$ vectors by the Steinitz theorem. Choose an independent family $u_1, \dots, u_k$ in $U$ with $k$ as large as possible. Each $u \in U$ lies in the span of the $u_i$: otherwise the family $u_1, \dots, u_k, u$ is independent by the test of Section 1, and it is larger. So the $u_i$ form a basis of $U$, and $\dim U = k \le n$. If $k = n$, extend $u_1, \dots, u_k$ to a basis of $V$. The extended basis has $n$ vectors, so the extension adds none. Thus the $u_i$ form a basis of $V$, and $U = V$. $\square$

::: mathlib
`Submodule.finrank_le` · `Mathlib.LinearAlgebra.Dimension.Constructions`

The bound `finrank R ↥s ≤ finrank R M` for a submodule of a finite module, over a ring with the strong rank condition.

<?decl Submodule.finrank_le?>
:::

**Theorem (Rank-nullity).** Let $V$ be finite dimensional and $f : V \to W$ linear. Then $\operatorname{im} f$ is finite dimensional and
$$\dim \operatorname{im} f + \dim \ker f = \dim V.$$

*Proof.* The kernel is a subspace of $V$, so it has a basis $u_1, \dots, u_k$ with $k = \dim \ker f$, by the last theorem. Extend it to a basis $u_1, \dots, u_k, v_1, \dots, v_r$ of $V$, by Section 2. Then $\dim V = k + r$. It suffices to show that $f(v_1), \dots, f(v_r)$ is a basis of $\operatorname{im} f$.

They span the image. Let $y = f(x)$ with $x \in V$. Write $x = \sum_i a_i u_i + \sum_j b_j v_j$. Then $f(x) = \sum_i a_i f(u_i) + \sum_j b_j f(v_j) = \sum_j b_j f(v_j)$, since $f(u_i) = 0$.

They are independent. Suppose $\sum_j c_j f(v_j) = 0$. Then $f(\sum_j c_j v_j) = 0$, so $\sum_j c_j v_j \in \ker f$. So there are scalars $d_i$ with $\sum_j c_j v_j = \sum_i d_i u_i$, that is,
$$\sum_i d_i u_i - \sum_j c_j v_j = 0.$$
This is a relation among the vectors of a basis of $V$, so all the coefficients are $0$. In particular $c_j = 0$ for each $j$.

So $\dim \operatorname{im} f = r = \dim V - \dim \ker f$. $\square$

::: mathlib
`LinearMap.finrank_range_add_finrank_ker` · `Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`

The statement `finrank K (range f) + finrank K (ker f) = finrank K V` for `f : V →ₗ[K] V₂` and `[Module.Finite K V]`. The hypotheses are `[HasRankNullity K]` and `[StrongRankCondition K]`, which hold for each division ring. Note the order of the two terms: the range comes first.

<?decl LinearMap.finrank_range_add_finrank_ker?>
:::

The theorem also holds for each space $V$, with the dimensions as cardinals. The proof is the same: extend a basis of $\ker f$ to a basis of $V$, and the images of the new vectors form a basis of the range. The sum of cardinals then replaces the sum of numbers.

::: mathlib
`LinearMap.rank_range_add_rank_ker` · `Mathlib.LinearAlgebra.Dimension.RankNullity`

The form with cardinals: `rank R (range f) + rank R (ker f) = rank R M`. It needs no finiteness. It holds over each ring with the class `HasRankNullity`.

<?decl LinearMap.rank_range_add_rank_ker?>
:::

::: mathlib
`HasRankNullity` · `Mathlib.LinearAlgebra.Dimension.RankNullity`

The class `HasRankNullity R` asks two things of each `R`-module `M`: that some independent set has the cardinal `rank R M`, and that `rank (M ⧸ N) + rank N = rank M` for each submodule `N`. Mathlib proves the rank-nullity theorems once from this class. The instances are `DivisionRing.hasRankNullity` and `IsDomain.hasRankNullity`, for commutative domains. The integers are a commutative domain, so $\operatorname{rank}_{\mathbb{Z}}$ also satisfies rank-nullity.

<?decl HasRankNullity?>
:::

**Corollary (Quotients).** Let $V$ be finite dimensional and $U$ a subspace. Then $\dim (V / U) + \dim U = \dim V$.

*Proof.* Apply rank-nullity to the quotient map $\pi : V \to V / U$. It is surjective, so $\operatorname{im} \pi = V / U$, and $\ker \pi = U$ by Chapter 1. $\square$

::: mathlib
`Submodule.finrank_quotient_add_finrank` · `Mathlib.LinearAlgebra.Dimension.RankNullity`

The statement `finrank R (M ⧸ N) + finrank R N = finrank R M` for a finite module over a ring with the two classes of rank-nullity.

<?decl Submodule.finrank_quotient_add_finrank?>
:::

**Corollary (Dimension of a sum).** Let $U_1, U_2$ be finite dimensional subspaces of $V$. Then
$$\dim (U_1 + U_2) + \dim (U_1 \cap U_2) = \dim U_1 + \dim U_2.$$

*Proof.* Let $g : U_1 \times U_2 \to V$, $g(x, y) = x + y$. It is linear, and its range is $U_1 + U_2$. Its kernel is the set of the pairs $(x, -x)$ with $x \in U_1 \cap U_2$, and the map $x \mapsto (x, -x)$ is an isomorphism from $U_1 \cap U_2$ onto it. The product $U_1 \times U_2$ has dimension $\dim U_1 + \dim U_2$: the union of a basis of $U_1 \times 0$ and a basis of $0 \times U_2$ is a basis. Rank-nullity for $g$ gives the formula. $\square$

::: mathlib
`Submodule.finrank_sup_add_finrank_inf_eq` · `Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`

The statement `finrank K ↥(s ⊔ t) + finrank K ↥(s ⊓ t) = finrank K ↥s + finrank K ↥t`, for finite dimensional subspaces of a space over a division ring.

<?decl Submodule.finrank_sup_add_finrank_inf_eq?>
:::

**Corollary (Injective and surjective).** Let $V$ and $W$ be finite dimensional with $\dim V = \dim W$, and let $f : V \to W$ be linear. Then $f$ is injective if and only if it is surjective, if and only if it is bijective. In particular this holds for each endomorphism of $V$.

*Proof.* The map $f$ is injective if and only if $\dim \ker f = 0$. By rank-nullity this holds if and only if $\dim \operatorname{im} f = \dim V = \dim W$. By the theorem on subspaces, this holds if and only if $\operatorname{im} f = W$, that is, if $f$ is surjective. $\square$

::: mathlib
`LinearMap.injective_iff_surjective` · `Mathlib.LinearAlgebra.FiniteDimensional.Basic`

For an endomorphism `f : V →ₗ[K] V` of a finite dimensional space: `Injective f ↔ Surjective f`. The version for two spaces of the same dimension is `LinearMap.injective_iff_surjective_of_finrank_eq_finrank`.

<?decl LinearMap.injective_iff_surjective?>
:::

**Corollary (Homogeneous systems).** If $\dim W < \dim V$, then each linear map $f : V \to W$ has a nonzero kernel. A homogeneous linear system with fewer equations than unknowns has a nonzero solution.

*Proof.* $\dim \ker f = \dim V - \dim \operatorname{im} f \ge \dim V - \dim W > 0$, since $\operatorname{im} f \subseteq W$. For the system, take the map $K^n \to K^m$ with $m < n$ that sends the unknowns to the left sides of the equations. $\square$

**Corollary (Classification).** Two finite dimensional spaces over $K$ are isomorphic if and only if they have the same dimension. Each space of dimension $n$ is isomorphic to $K^n$.

*Proof.* Isomorphic spaces have the same dimension, since a linear equivalence sends a basis to a basis. Conversely, let $(b_1, \dots, b_n)$ be a basis of $V$ and $(c_1, \dots, c_n)$ a basis of $W$. The linear map $f$ with $f(b_i) = c_i$, from the universal property of a basis, has an inverse: the linear map $g$ with $g(c_i) = b_i$. Indeed $g \circ f$ and the identity agree on the basis $(b_i)$, so they are equal, and the same holds for $f \circ g$. $\square$

::: mathlib
`FiniteDimensional.nonempty_linearEquiv_of_finrank_eq` · `Mathlib.LinearAlgebra.Dimension.Free`

The statement `finrank R M = finrank R M' → Nonempty (M ≃ₗ[R] M')` for finite free modules. The conclusion is `Nonempty`, a proposition: the equivalence depends on a choice of bases, and Mathlib does not pick one. To get the equivalence as data, use `LinearEquiv.ofFinrankEq`.

<?decl FiniteDimensional.nonempty_linearEquiv_of_finrank_eq?>
:::

### Examples

**Example (A map from $\mathbb{Q}^4$ to $\mathbb{Q}^3$).** Let
$$f(x_1, x_2, x_3, x_4) = (x_1 + x_2 + x_4, \ x_2 + x_3, \ x_1 - x_3 + x_4).$$
The third coordinate is the first minus the second. So the range lies in the plane $P = \{y : y_3 = y_1 - y_2\}$. It is all of $P$: $f(e_1) = (1, 0, 1)$ and $f(e_3) = (0, 1, -1)$ are independent vectors of $P$, and $P$ has dimension $2$. So $\dim \operatorname{im} f = 2$, and rank-nullity gives $\dim \ker f = 4 - 2 = 2$. Directly, the kernel is given by $x_2 = -x_3$ and $x_1 = -x_2 - x_4 = x_3 - x_4$, so it is $\{(s - t, -s, s, t) : s, t \in \mathbb{Q}\}$, with the basis $(1, -1, 1, 0)$ and $(-1, 0, 0, 1)$. The third equation holds on it: $(s - t) - s + t = 0$.

**Example (Two planes in $\mathbb{R}^4$).** Let $U_1 = \operatorname{span}\{e_1, e_2\}$ and $U_2 = \operatorname{span}\{e_2 + e_3, e_4\}$. The sum $U_1 + U_2$ contains $e_1$, $e_2$, $e_4$ and $e_3 = (e_2 + e_3) - e_2$, so it is $\mathbb{R}^4$. The formula gives $\dim (U_1 \cap U_2) = 2 + 2 - 4 = 0$. Check: a vector $a e_1 + b e_2 = c(e_2 + e_3) + d e_4$ needs $a = 0$, $b = c$, $c = 0$ and $d = 0$. Now replace $U_2$ by $U_2' = \operatorname{span}\{e_2, e_3\}$. Then $U_1 + U_2' = \operatorname{span}\{e_1, e_2, e_3\}$ has dimension $3$, so $\dim (U_1 \cap U_2') = 1$, and indeed $U_1 \cap U_2' = \mathbb{R} e_2$. Two planes in a space of dimension $4$ can meet only in $0$. In a space of dimension $3$ they meet at least in a line, since $\dim (U_1 \cap U_2) \ge 2 + 2 - 3$.

**Example (Interpolation).** Let $a_0, \dots, a_n$ be distinct real numbers and $P_n$ the polynomials of degree at most $n$. The map $\mathrm{ev} : P_n \to \mathbb{R}^{n+1}$, $p \mapsto (p(a_0), \dots, p(a_n))$, is linear. Its kernel is $0$: a nonzero polynomial of degree at most $n$ has at most $n$ roots. Both spaces have dimension $n + 1$. So $\mathrm{ev}$ is surjective by the corollary: for each list of values $b_0, \dots, b_n$ there is exactly one polynomial $p \in P_n$ with $p(a_i) = b_i$. The proof gives existence from uniqueness, with no formula. Lagrange's formula is one explicit inverse.

**Counterexample (Infinite dimension).** Let $V = \mathbb{R}[x]$ and $f(p) = x p$. Then $f$ is injective, but not surjective: the constant $1$ is not a multiple of $x$. The derivative $D$ is surjective but not injective. So the corollary on injectivity fails in infinite dimension. In Mathlib, `LinearMap.injective_iff_surjective` asks for `[FiniteDimensional K V]`, and the hypothesis is needed.

### The library around it

The definition of `finrank` and its basic lemmas are in `Mathlib.LinearAlgebra.Dimension.Finrank`. The rank-nullity theorem for cardinals and the class `HasRankNullity` are in `Mathlib.LinearAlgebra.Dimension.RankNullity`. The finite dimensional theory over a division ring is in `Mathlib.LinearAlgebra.FiniteDimensional.Defs`, `Mathlib.LinearAlgebra.FiniteDimensional.Lemmas` and `Mathlib.LinearAlgebra.FiniteDimensional.Basic`. The dimensions of products, of function spaces and of subspaces are in `Mathlib.LinearAlgebra.Dimension.Constructions`.

The tactic of choice is to reduce a statement on dimensions to `omega`: collect the equations from rank-nullity and the bounds from `Submodule.finrank_le`, then let `omega` do the arithmetic in `ℕ`.

### Exercises

1. (A) Find the dimension of the kernel of $f : \mathbb{R}^5 \to \mathbb{R}^2$, $f(x) = (x_1 + x_2, x_3 + x_4 + x_5)$, without solving the system.
2. (A) Show that a linear map $\mathbb{R}^2 \to \mathbb{R}^3$ is never surjective, and a linear map $\mathbb{R}^3 \to \mathbb{R}^2$ is never injective.
3. (A) Let $U_1$ and $U_2$ be subspaces of dimension $5$ in $\mathbb{R}^8$. Show that $\dim (U_1 \cap U_2) \ge 2$.
4. (B) Let $f : V \to W$ and $g : W \to X$ be linear, with $V$ and $W$ finite dimensional. Show that $\dim \ker (g \circ f) \le \dim \ker f + \dim \ker g$. Hint: apply rank-nullity to the restriction of $f$ to $\ker(g \circ f)$.
5. (B) Show that the space of the $n \times n$ real matrices with trace $0$ has dimension $n^2 - 1$.
6. (B) Let $p \in \mathbb{R}[x]$ have degree $d$. Show that the map $P_n \to P_{n+d}$, $q \mapsto p q$, is injective, and find the dimension of the quotient $P_{n+d} / p P_n$.
7. (B) Let $V$ be finite dimensional and $f \in \operatorname{End}(V)$. Show that $V = \ker f \oplus \operatorname{im} f$ if and only if $\ker f \cap \operatorname{im} f = 0$. Hint: compute $\dim(\ker f + \operatorname{im} f)$.
8. (C) Let $f \in \operatorname{End}(V)$ with $V$ finite dimensional. Show that the kernels $\ker f \subseteq \ker f^2 \subseteq \dots$ become constant, and that the dimensions of the steps $\dim \ker f^{k+1} - \dim \ker f^{k}$ do not increase with $k$. Hint: apply rank-nullity to $f$ restricted to $\operatorname{im} f^k$.

### Notes and history

The count of free unknowns in a linear system goes back to the work of Frobenius and of Kronecker on the rank of a matrix in the 1870s. The name "nullity" for the dimension of the kernel is due to James Joseph Sylvester, who also named the "law of nullity" in 1884. The form with dimensions of abstract spaces is in the books of the 1930s and 1940s, for example in Halmos's "Finite-dimensional vector spaces" of 1942.

The class `HasRankNullity` lets one proof serve fields, division rings and commutative domains. The choice to set `finrank` to `0` in infinite dimension follows the convention of `Nat.card`, and it lets the formulas use natural numbers with no case split.

### Reference

<?reference?>
