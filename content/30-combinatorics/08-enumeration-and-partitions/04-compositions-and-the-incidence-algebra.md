---
title: Compositions and the incidence algebra
kind: api
modules:
  - Mathlib.Combinatorics.Enumerative.Composition
  - Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
explains:
  E2: [composition_card, compositionAsSetEquiv, Composition.blocksFinEquiv, List.flatten_splitWrtComposition, IncidenceAlgebra.zeta_mul_zeta, IncidenceAlgebra.mu_mul_zeta, IncidenceAlgebra.moebius_inversion_top, IncidenceAlgebra.mu_prod_mu]
  E1: auto
families: []
requires: [V03.C02, V03.C03, V03.C06, V04.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Compositions and the incidence algebra

### Overview

A composition of a natural number $n$ is an ordered sum $n = i_0 + i_1 + \dots + i_{k-1}$ of positive integers. It is a partition of $n$ in which the order of the parts matters, so $3 = 1 + 2$ and $3 = 2 + 1$ are two different compositions and one partition. A composition of $n$ is the same as a cut of the row $0, 1, \dots, n - 1$ into consecutive blocks, and the parts are the lengths of the blocks. From this picture the number of compositions of $n \geq 1$ is $2^{n-1}$: a composition is a choice of the cut points among the $n - 1$ gaps of the row.

The incidence algebra of a locally finite order $\alpha$ is the ring of functions $f(a, b)$ on the pairs $a \leq b$, with a product that sums over the points of the interval $[a, b]$. Its zeta function is $1$ on each pair $a \leq b$, and its inverse is the Möbius function $\mu$. The inverse gives the principle of Möbius inversion: when $g(x) = \sum_{y \geq x} f(y)$ for all $x$, then $f(x) = \sum_{y \geq x} \mu(x, y)\, g(y)$. The principle of inclusion and exclusion of Section 3 is the case of the lattice of subsets.

The two modules of this section are independent of each other. They both count with finite sets and sums from Volume 3, and the incidence algebra uses the finite intervals `Finset.Icc a b` of a locally finite order from Volume 4.

### The library around it

#### Compositions as lists of blocks

The module `Mathlib.Combinatorics.Enumerative.Composition` defines `Composition n` as a structure with a list `blocks : List ℕ` and two proofs: `Composition.blocks_pos` (each block is positive) and `Composition.blocks_sum` (the blocks add up to $n$). Two compositions are equal when their lists are equal (`Composition.ext`). The number of blocks is `c.length`, and `Composition.length_le` bounds it by $n$. For finite sums and products the module also has the function form `c.blocksFun : Fin c.length → ℕ`, with `Composition.sum_blocksFun` stating $\sum_i c_i = n$.

The block structure on $\{0, \dots, n - 1\}$ is computed from partial sums. The function `c.sizeUpTo i` is the sum of the first $i$ blocks. It is monotone (`Composition.monotone_sizeUpTo`) and `Composition.sizeUpTo_succ` adds one block at a time. The $i$-th block starts at `c.sizeUpTo i`. The order embedding `c.embedding i : Fin (c.blocksFun i) ↪o Fin n` sends the $j$-th point of the block $i$ to `c.sizeUpTo i + j`. In the other direction, `c.index j` is the block that contains the point $j$, and `c.invEmbedding j` is the position of $j$ inside its block. The two directions are inverse: `Composition.embedding_comp_inv` and `Composition.index_embedding`. The ranges of the embeddings of two different blocks are disjoint (`Composition.disjoint_range`), and each point is in the range of its own block (`Composition.mem_range_embedding`).

**Theorem.** For a composition $c$ of $n$ there is a bijection between the pairs $(i, j)$ with $i$ a block and $j < c_i$, and the set $\{0, \dots, n - 1\}$.

*Proof.* Send $(i, j)$ to `c.embedding i j`. The map is injective, because two different blocks have disjoint ranges and each embedding is injective. Its inverse sends $j$ to `(c.index j, c.invEmbedding j)`, by the two inverse laws above. $\square$

This is `Composition.blocksFinEquiv`, an equivalence `(Σ i : Fin c.length, Fin (c.blocksFun i)) ≃ Fin n`. The product form `Composition.prod_prod_apply_embedding` states $\prod_i \prod_j a(\mathrm{emb}_i(j)) = \prod_k a(k)$ in a commutative monoid.

#### Special compositions and operations

| Lean name | Composition |
|---|---|
| `Composition.ones n` | $1 + 1 + \dots + 1$, with $n$ blocks |
| `Composition.single n h` | the one block $n$, for $0 < n$ |
| `c₁.append c₂` | the blocks of $c_1$, then the blocks of $c_2$, a composition of $m + n$ |
| `c.reverse` | the blocks in the reverse order |
| `c.cast h` | the same blocks, seen as a composition of $n$ when $h : m = n$ |

The reverse is an involution (`Composition.reverse_reverse`), it fixes `ones n` (`Composition.reverse_ones`), and it reverses an append (`Composition.reverse_append`, with a cast of the sum $m + n$ to $n + m$). The lemma `Composition.sigma_eq_iff_blocks_eq` avoids casts: two elements of the sigma type `Σ n, Composition n` are equal when their block lists are equal. Two recursors, `Composition.recOnSingleAppend` and `Composition.recOnAppendSingle`, build a function on all compositions from its value on the empty composition of $0$ and a step that adds one block at the front or at the back. A composition differs from `ones n` exactly when it has a block greater than $1$ (`Composition.ne_ones_iff`).

#### Splitting a list

A composition of the length of a list cuts the list into slices. The function `List.splitWrtComposition l c` returns the list of slices, one for each block, and it has `c.length` slices (`List.length_splitWrtComposition`).

**Theorem.** Splitting a list $l$ by a composition of its length and then flattening the result gives $l$ back. Conversely, flattening a list of nonempty lists $L$ and splitting by the composition of their lengths gives $L$ back.

*Proof sketch.* Both statements go by induction on the list of blocks. A step takes the first $c_0$ elements of $l$ as the first slice and splits the rest by the remaining blocks. The first statement holds at each step, because the first $c_0$ elements followed by the rest is the list itself. For the second statement, the first block equals the length of the first list of $L$, so the first slice is exactly that list. $\square$

The two directions are `List.flatten_splitWrtComposition` and `List.splitWrtComposition_flatten`. The second needs the hypothesis `List.map List.length L = c.blocks`.

#### Compositions as sets and their number

The second model is `CompositionAsSet n`. Its field `boundaries : Finset (Fin (n + 1))` is a set of cut points that contains $0$ and $n$. A composition gives its set of partial sums `c.boundaries`, with `c.length + 1` elements, and the two models are equivalent by `compositionEquiv n : Composition n ≃ CompositionAsSet n`, built from `Composition.toCompositionAsSet` and `CompositionAsSet.toComposition`.

**Theorem.** For every $n$, the number of compositions of $n$ is $2^{n - 1}$, where $n - 1$ is the truncated subtraction of `ℕ`.

*Proof.* A set of cut points always contains $0$ and $n$. Remove these two points. The rest is an arbitrary subset of the $n - 1$ inner points $\{1, \dots, n - 1\}$, and each subset arises from exactly one set of cut points. This gives a bijection between `CompositionAsSet n` and the subsets of `Fin (n - 1)`, so `CompositionAsSet n` has $2^{n-1}$ elements. The equivalence `compositionEquiv n` transfers the count to `Composition n`. For $n = 0$ the empty composition is the only one, and $2^{0 - 1} = 2^0 = 1$ in `ℕ`. $\square$

The bijection is `compositionAsSetEquiv n : CompositionAsSet n ≃ Finset (Fin (n - 1))`, and the counts are `compositionAsSet_card` and `composition_card`. The instance `compositionFintype` makes `Composition n` a finite type. The partitions of Section 2 are the compositions up to order: `Nat.Partition.ofComposition` sorts the blocks into a multiset.

#### The incidence algebra

The module `Mathlib.Combinatorics.Enumerative.IncidenceAlgebra` defines `IncidenceAlgebra 𝕜 α` for a type `α` with `≤` and a type `𝕜` with `0`. An element is a function `f : α → α → 𝕜` with the field `eq_zero_of_not_le'`: $f(a, b) = 0$ unless $a \leq b$. The element acts as a function of two variables by a coercion, and `IncidenceAlgebra.apply_eq_zero_of_not_le` is the field in the simp normal form `f a b`. Extensionality `IncidenceAlgebra.ext` asks for equality only on the pairs $a \leq b$, because the other values are $0$.

The addition and the scalar multiplication are pointwise (`IncidenceAlgebra.constSMul_apply` and the instance `IncidenceAlgebra.moduleRight`). The unit is the delta function, `IncidenceAlgebra.one_apply : 1 a b = if a = b then 1 else 0`. The product is the convolution over the interval:

$$(f * g)(a, b) = \sum_{a \leq x \leq b} f(a, x)\, g(x, b),$$

which is `IncidenceAlgebra.mul_apply`, with the sum over `Finset.Icc a b`. The sum is finite because the order is locally finite. With these operations the type is a ring (`IncidenceAlgebra.instRing`) over a ring `𝕜`, and an algebra over a commutative semiring (`IncidenceAlgebra.algebraRight`). For a finite order it is the ring of upper triangular matrices with respect to a linear extension of the order, and the delta function is the identity matrix. The library does not state this matrix form.

The zeta function `IncidenceAlgebra.zeta 𝕜` has the value $1$ at $a \leq b$ (`IncidenceAlgebra.zeta_apply`, `IncidenceAlgebra.zeta_of_le`). Convolution with it sums over intervals.

**Theorem.** For $a \leq b$, $(\zeta * \zeta)(a, b) = |[a, b]|$.

*Proof.* By the formula for the product, $(\zeta * \zeta)(a, b) = \sum_{x \in [a, b]} \zeta(a, x)\, \zeta(x, b)$. For $x \in [a, b]$ both factors are $1$, so the sum counts the points of $[a, b]$. $\square$

This is `IncidenceAlgebra.zeta_mul_zeta`, with the cast of `(Finset.Icc a b).card` into `𝕜`. The element `IncidenceAlgebra.lambda 𝕜` is $1$ on the pairs where $b$ covers or equals $a$, and $0$ elsewhere.

#### The Möbius function and inversion

The Möbius function `IncidenceAlgebra.mu 𝕜` is defined by recursion on the interval: $\mu(a, a) = 1$, and for $a < b$,

$$\mu(a, b) = -\sum_{a \leq x < b} \mu(a, x).$$

This is `IncidenceAlgebra.mu_apply`, with the special cases `IncidenceAlgebra.mu_self` and `IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne`.

**Theorem.** In a partial order, $\mu * \zeta = 1$ and $\zeta * \mu = 1$.

*Proof.* For $a \leq b$, $(\mu * \zeta)(a, b) = \sum_{x \in [a, b]} \mu(a, x)$. If $a = b$ the sum is $\mu(a, a) = 1$. If $a < b$ the sum is $\mu(a, b) + \sum_{a \leq x < b} \mu(a, x)$, which is $0$ by the recursion. So $\mu * \zeta = 1$. A second function $\mu'$ with the mirror recursion $\mu'(a, b) = -\sum_{a < x \leq b} \mu'(x, b)$ satisfies $\zeta * \mu' = 1$ by the same argument. In a ring a left inverse and a right inverse of the same element are equal: $\mu = \mu * (\zeta * \mu') = (\mu * \zeta) * \mu' = \mu'$. So $\zeta * \mu = 1$ as well. $\square$

The two identities are `IncidenceAlgebra.mu_mul_zeta` and `IncidenceAlgebra.zeta_mul_mu`. Their values at a pair give the sums `IncidenceAlgebra.sum_Icc_mu_right` and `IncidenceAlgebra.sum_Icc_mu_left`, and the mirror recursion is `IncidenceAlgebra.mu_eq_neg_sum_Ioc_of_ne`. The Möbius function of the dual order is the transpose: `IncidenceAlgebra.mu_toDual` states $\mu_{\alpha^{op}}(a, b) = \mu_\alpha(b, a)$.

**Theorem (Möbius inversion).** Let $\alpha$ be a locally finite partial order with a top element, and let $f, g : \alpha \to 𝕜$ with $g(x) = \sum_{y \geq x} f(y)$ for all $x$. Then $f(x) = \sum_{y \geq x} \mu(x, y)\, g(y)$ for all $x$.

*Proof.* Substitute the formula for $g$:
$$\sum_{y \geq x} \mu(x, y)\, g(y) = \sum_{y \geq x} \sum_{z \geq y} \mu(x, y)\, f(z) = \sum_{z \geq x} \Big( \sum_{x \leq y \leq z} \mu(x, y) \Big) f(z).$$
The inner sum is $(\mu * \zeta)(x, z) = 1(x, z)$, which is $1$ for $z = x$ and $0$ otherwise. So the sum is $f(x)$. The top element makes the sums over $\{y \geq x\}$ finite. $\square$

This is `IncidenceAlgebra.moebius_inversion_top`. The dual form `IncidenceAlgebra.moebius_inversion_bot` uses a bottom element and sums over $\{y \leq x\}$, with $f(x) = \sum_{y \leq x} \mu(y, x)\, g(y)$. On the chain $\mathbb{N}$, the Möbius function is $1$ on the diagonal, $-1$ on the pairs $(a, a + 1)$ and $0$ elsewhere, and the inversion recovers a sequence from its partial sums by differences.

#### Products and the Euler characteristic

The product order on $\alpha \times \beta$ has the incidence algebra of the product. The element `f.prod g` has the value $f(a_1, a_2)\, g(b_1, b_2)$ at the pair $((a_1, b_1), (a_2, b_2))$ (`IncidenceAlgebra.prod_apply`). The product is multiplicative over a commutative ring (`IncidenceAlgebra.prod_mul_prod`), it sends $1$ to $1$ (`IncidenceAlgebra.one_prod_one`) and $\zeta$ to $\zeta$ (`IncidenceAlgebra.zeta_prod_zeta`).

**Theorem.** The Möbius function of a product of two partial orders is the product of the Möbius functions: $\mu_{\alpha \times \beta}((a_1, b_1), (a_2, b_2)) = \mu_\alpha(a_1, a_2)\, \mu_\beta(b_1, b_2)$.

*Proof.* By the multiplicativity, $(\mu \times \mu) * (\zeta \times \zeta) = (\mu * \zeta) \times (\mu * \zeta) = 1 \times 1 = 1$. Since $\zeta \times \zeta$ is the zeta function of the product, $\mu \times \mu$ is a left inverse of it. The inverse of $\zeta$ is unique, so $\mu \times \mu$ is the Möbius function of the product. $\square$

This is `IncidenceAlgebra.mu_prod_mu`. The lattice of subsets of a set with $n$ elements is the product of $n$ copies of the chain $\{0 < 1\}$, whose Möbius function is $-1$ on the pair $(0, 1)$. So the product theorem gives $\mu(s, t) = (-1)^{|t \setminus s|}$ for $s \subseteq t$, and Möbius inversion on the subsets is inclusion and exclusion. The library does not state this value of $\mu$ on `Finset α`. For a bounded order, `IncidenceAlgebra.eulerChar 𝕜 α` is $\mu(\bot, \top)$. It is invariant under the order dual (`IncidenceAlgebra.eulerChar_orderDual`) and multiplicative on products (`IncidenceAlgebra.eulerChar_prod`).

#### Common errors

1. A learner writes a statement about `Composition (m + n)` and another about `Composition (n + m)` and expects them to match. The two types are different, and a composition must be moved by `Composition.cast`. Statements about the sigma type `Σ n, Composition n` with `Composition.sigma_eq_iff_blocks_eq` avoid the problem.
2. A learner applies `IncidenceAlgebra.mu_mul_zeta` in a preorder that is not a partial order. The definition of `mu` works in a preorder, but the inverse laws need antisymmetry, and the instances ask for `PartialOrder α`.
3. A learner tries `IncidenceAlgebra.moebius_inversion_top` on `ℕ`. The order `ℕ` has no top, so the hypothesis `OrderTop α` fails, and the sums over `Finset.Ici x` are not defined. Use `IncidenceAlgebra.moebius_inversion_bot` on `ℕ`.

### Exercises

1. (A) List the compositions of $4$ and check that there are $2^3 = 8$ of them. For each one, write its set of cut points.
2. (A) Compute `c.sizeUpTo i`, `c.index j` and `c.invEmbedding j` for all $i$ and $j$ when $c$ is the composition $2 + 1 + 3$ of $6$.
3. (B) Prove that the number of compositions of $n$ with exactly $k$ blocks is $\binom{n-1}{k-1}$ for $1 \leq k \leq n$, by the cut points.
4. (B) Compute $\mu(a, b)$ on the chain $\mathbb{N}$ from the recursion of `IncidenceAlgebra.mu_apply`, and deduce $f(n) = g(n) - g(n - 1)$ from `IncidenceAlgebra.moebius_inversion_bot` when $g(n) = \sum_{k \leq n} f(k)$.
5. (B) Compute $(\zeta * \zeta * \zeta)(a, b)$ on a chain, as a binomial coefficient in the number of points of $[a, b]$.
6. (C) Use `IncidenceAlgebra.mu_prod_mu` and the chain $\{0 < 1\}$ to prove $\mu(s, t) = (-1)^{|t \setminus s|}$ for subsets $s \subseteq t$, and derive the principle of inclusion and exclusion from Möbius inversion.

### Reference

<?reference?>
