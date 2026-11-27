---
title: The open mapping and closed graph theorems
kind: theory
modules:
  - Mathlib.Analysis.Normed.Operator.Banach
explains:
  E3: [ContinuousLinearMap.exists_approx_preimage_norm_le, ContinuousLinearMap.exists_preimage_norm_le, ContinuousLinearMap.isOpenMap, ContinuousLinearEquiv.ofBijective, LinearMap.continuous_of_isClosed_graph]
  E2: [LinearEquiv.continuous_symm, LinearEquiv.toContinuousLinearEquivOfContinuous, ContinuousLinearMap.isQuotientMap, ContinuousLinearMap.ofIsClosedGraph, LinearMap.continuous_of_seq_closed_graph, ContinuousLinearMap.isClosed_range_iff_antilipschitz_of_injective, ContinuousLinearMap.isUnit_iff_bijective, ContinuousLinearMap.closed_complemented_range_of_isCompl_of_ker_eq_bot]
  E1: auto
families: []
requires: [V07, V13, V16.C01, V16.C02, V16.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The open mapping and closed graph theorems

### Overview

A bounded linear bijection between finite dimensional spaces has a bounded inverse, by Chapter 3. For infinite dimensional spaces this is false in general, and the open mapping theorem of Banach restores it for Banach spaces: a surjective bounded operator between Banach spaces maps open sets to open sets, so a bijective one has a bounded inverse. The proof has two steps. The Baire step uses the completeness of the target to show that the closure of the image of a ball contains a ball. The step of successive approximation uses the completeness of the domain to remove the closure. Two consequences follow. The closed graph theorem says that a linear map between Banach spaces with a closed graph is bounded. And two complete norms on one space, one of them dominated by the other, are equivalent.

### Definitions

**Definition (Open map).** A map $f : X \to Y$ of topological spaces is *open* if $f(U)$ is open for each open $U \subseteq X$.

For a linear map $T : E \to F$ of normed spaces, $T$ is open if and only if $T(B(0, 1))$ contains a ball $B(0, \delta)$ (Exercise 2). An open linear map is surjective, since its image is an open subspace and an open subspace contains a ball around $0$, which spans $F$.

**Definition (Graph).** The *graph* of a map $T : E \to F$ is $G(T) = \{(x, Tx) : x \in E\} \subseteq E \times F$. The graph is *closed* if it is closed for the product topology. For a linear $T$ this says: if $x_n \to x$ and $Tx_n \to y$, then $y = Tx$.

A continuous map into a Hausdorff space has a closed graph. The point of the closed graph theorem is the converse, which is false for general maps: $f(x) = 1/x$ for $x \ne 0$ and $f(0) = 0$ has a closed graph in $\mathbb{R}^2$ and is not continuous.

::: mathlib
`LinearMap.graph` · `Mathlib.LinearAlgebra.Prod`

`f.graph : Submodule R (M × M₂)`, the graph of a linear map as a submodule of the product, with `LinearMap.mem_graph_iff : x ∈ f.graph ↔ x.2 = f x.1`. The closed graph theorem takes the hypothesis `IsClosed (g.graph : Set (E × F))`, with the product norm of Chapter 1.

<?decl LinearMap.graph?>
:::

### Theorems and proofs

**Theorem (Approximate preimages).** Let $E$ be a normed space, $F$ a Banach space and $T \in L(E, F)$ surjective. Then there is $C \ge 0$ such that for each $y \in F$ there is $x \in E$ with
$$\|Tx - y\| \le \tfrac12\|y\| \quad\text{and}\quad \|x\| \le C\|y\|.$$

*Proof.* Since $T$ is surjective, $F = \bigcup_n T(B(0, n))$, so $F = \bigcup_n\overline{T(B(0, n))}$, a countable union of closed sets. The space $F$ is complete, so by the Baire category theorem some $\overline{T(B(0, n))}$ contains a ball $B(y_0, \varepsilon)$.

Claim: $B(0, \varepsilon) \subseteq \overline{T(B(0, 2n))}$. Let $\|y\| < \varepsilon$. Then $y_0 + y$ and $y_0$ are limits of sequences $Tu_k$ and $Tv_k$ with $\|u_k\|, \|v_k\| < n$. So $y$ is the limit of $T(u_k - v_k)$ with $\|u_k - v_k\| < 2n$.

Now let $y \ne 0$ (for $y = 0$ take $x = 0$). The vector $y' = \frac{\varepsilon}{2\|y\|}y$ has $\|y'\| = \varepsilon/2 < \varepsilon$, so by the claim there is $x'$ with $\|x'\| < 2n$ and $\|Tx' - y'\| \le \frac12\|y'\|$. Put $x = \frac{2\|y\|}{\varepsilon}x'$. Then $\|x\| \le \frac{4n}{\varepsilon}\|y\|$ and
$$\|Tx - y\| = \frac{2\|y\|}{\varepsilon}\|Tx' - y'\| \le \frac{2\|y\|}{\varepsilon}\cdot\frac12\cdot\frac{\varepsilon}{2} = \frac12\|y\|.$$
So $C = 4n/\varepsilon$ works. $\square$

::: mathlib
`ContinuousLinearMap.exists_approx_preimage_norm_le` · `Mathlib.Analysis.Normed.Operator.Banach`

`f.exists_approx_preimage_norm_le surj : ∃ C ≥ 0, ∀ y, ∃ x, dist (f x) y ≤ 1 / 2 * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖`, with `[CompleteSpace F]` only. The Mathlib file calls it the first step of the proof of the open mapping theorem, and it uses the Baire theorem in the same form as the proof above.

<?decl ContinuousLinearMap.exists_approx_preimage_norm_le?>
:::

**Theorem (Bounded preimages).** Let $E$ and $F$ be Banach spaces and $T \in L(E, F)$ surjective. Then there is $K > 0$ such that each $y \in F$ has a preimage $x$ with $Tx = y$ and $\|x\| \le K\|y\|$.

*Proof.* Let $C$ be the constant of the last theorem and $y \in F$. Put $y_0 = y$. By induction choose $x_k$ with $\|Tx_k - y_k\| \le \frac12\|y_k\|$ and $\|x_k\| \le C\|y_k\|$, and put $y_{k+1} = y_k - Tx_k$. Then $\|y_{k+1}\| \le \frac12\|y_k\|$, so $\|y_k\| \le 2^{-k}\|y\|$ and $\|x_k\| \le C2^{-k}\|y\|$. The series $\sum_kx_k$ converges absolutely, so it converges in the Banach space $E$ to a vector $x$ with $\|x\| \le 2C\|y\|$. Since $Tx_k = y_k - y_{k+1}$, the partial sums telescope:
$$T\Big(\sum_{k \le N}x_k\Big) = y_0 - y_{N+1} \to y,$$
and the continuity of $T$ gives $Tx = y$. So $K = 2C + 1$ works. $\square$

::: mathlib
`ContinuousLinearMap.exists_preimage_norm_le` · `Mathlib.Analysis.Normed.Operator.Banach`

`f.exists_preimage_norm_le surj : ∃ C > 0, ∀ y, ∃ x, f x = y ∧ ‖x‖ ≤ C * ‖y‖`, with `[CompleteSpace F] [CompleteSpace E]`. A choice of such preimages is packaged as `ContinuousLinearMap.nonlinearRightInverseOfSurjective`, a right inverse that is bounded but in general not linear.

<?decl ContinuousLinearMap.exists_preimage_norm_le?>
:::

**Theorem (Open mapping theorem).** A surjective bounded operator between Banach spaces is an open map.

*Proof.* Let $U \subseteq E$ be open and $x \in U$, with $B(x, \delta) \subseteq U$. Let $K$ be the constant of the last theorem. If $\|y - Tx\| < \delta/K$, there is $z$ with $Tz = y - Tx$ and $\|z\| \le K\|y - Tx\| < \delta$, so $x + z \in U$ and $y = T(x + z) \in T(U)$. So $T(U)$ contains $B(Tx, \delta/K)$. $\square$

::: mathlib
`ContinuousLinearMap.isOpenMap` · `Mathlib.Analysis.Normed.Operator.Banach`

`f.isOpenMap surj : IsOpenMap f` for `f : E →SL[σ] F` between Banach spaces. The companion `ContinuousLinearMap.isQuotientMap` says that `F` carries the quotient topology of `f`, and `interior_preimage`, `closure_preimage` and `frontier_preimage` commute these operations with the preimage.

<?decl ContinuousLinearMap.isOpenMap?>
:::

**Corollary (Bounded inverse theorem).** Let $E$ and $F$ be Banach spaces and $T \in L(E, F)$ bijective. Then $T^{-1}$ is bounded, so $T$ is an isomorphism of normed spaces.

*Proof.* The inverse $T^{-1}$ is linear, and for an open $U \subseteq E$, $(T^{-1})^{-1}(U) = T(U)$ is open by the theorem. So $T^{-1}$ is continuous. $\square$

::: mathlib
`ContinuousLinearEquiv.ofBijective` · `Mathlib.Analysis.Normed.Operator.Banach`

`ContinuousLinearEquiv.ofBijective f (hinj : f.ker = ⊥) (hsurj : f.range = ⊤) : E ≃SL[σ] F`. The form for a linear equivalence that is continuous is `LinearEquiv.toContinuousLinearEquivOfContinuous`, built on `LinearEquiv.continuous_symm`. For an operator on one Banach space, `ContinuousLinearMap.isUnit_iff_bijective` says that `f` is a unit of the ring `E →L[𝕜] E` if and only if it is bijective.

<?decl ContinuousLinearEquiv.ofBijective?>
:::

**Corollary (Closed graph theorem).** Let $E$ and $F$ be Banach spaces and $T : E \to F$ linear with a closed graph. Then $T$ is bounded.

*Proof.* The product $E \times F$ with $\|(x, y)\| = \max(\|x\|, \|y\|)$ is a Banach space, and the graph $G = G(T)$ is a closed subspace, so $G$ is a Banach space (Section 1). The projection $p : G \to E$, $p(x, Tx) = x$, is linear, bounded with $\|p\| \le 1$ and bijective. By the bounded inverse theorem $p^{-1}$ is bounded: $\max(\|x\|, \|Tx\|) \le K\|x\|$ for a constant $K$. So $\|Tx\| \le K\|x\|$. $\square$

::: mathlib
`LinearMap.continuous_of_isClosed_graph` · `Mathlib.Analysis.Normed.Operator.Banach`

`g.continuous_of_isClosed_graph (hg : IsClosed (g.graph : Set (E × F))) : Continuous g` for a linear map between Banach spaces over the same field. The bundled form is `ContinuousLinearMap.ofIsClosedGraph`. The form in terms of sequences is `LinearMap.continuous_of_seq_closed_graph`: if `u → x` and `g ∘ u → y` imply `y = g x`, then `g` is continuous. In practice this is the form used, since it needs only the uniqueness of the limit.

<?decl LinearMap.continuous_of_isClosed_graph?>
:::

**Corollary (Comparable complete norms).** Let $\|\cdot\|_1$ and $\|\cdot\|_2$ be two norms on a vector space $E$ that both make $E$ complete, with $\|x\|_1 \le c\|x\|_2$ for all $x$. Then the norms are equivalent.

*Proof.* The identity $(E, \|\cdot\|_2) \to (E, \|\cdot\|_1)$ is a bounded bijection between Banach spaces, so its inverse is bounded: $\|x\|_2 \le c'\|x\|_1$. $\square$

### Examples

**Example (Projections onto closed complements).** Let $E$ be a Banach space and $E = M \oplus N$ an algebraic direct sum with $M$ and $N$ closed. Then the projection $P : E \to M$ along $N$ is bounded. Its graph is closed: if $x_n \to x$ and $Px_n \to y$, then $y \in M$ since $M$ is closed, and $x_n - Px_n \in N$ tends to $x - y$, so $x - y \in N$ since $N$ is closed. Hence $x = y + (x - y)$ is the decomposition of $x$, and $Px = y$. By the closed graph theorem $P$ is bounded. Mathlib uses the same idea in `ContinuousLinearMap.closed_complemented_range_of_isCompl_of_ker_eq_bot`.

**Counterexample (An incomplete domain for the inverse).** On $c_{00}$ with $\|\cdot\|_\infty$ let $T(x)_n = x_n/n$. Then $T$ is linear, bounded with $\|T\| = 1$, and bijective on $c_{00}$, with inverse $T^{-1}(x)_n = nx_n$. The inverse is not bounded, since $\|T^{-1}e_n\|_\infty = n$. So the bounded inverse theorem fails for the incomplete space $c_{00}$. On the Banach space $\ell^\infty$ the same $T$ is injective and bounded, but not surjective: the sequence $(1/\sqrt n)$ is in $\ell^\infty$, and its preimage $(\sqrt n)$ is not.

**Counterexample (A closed graph that is not bounded).** Let $E = C^1[0,1]$ with the norm $\|\cdot\|_\infty$, which is not complete, and $D : E \to C[0,1]$, $Df = f'$. The graph is closed: if $f_n \to f$ and $f_n' \to g$ uniformly, then $f(t) - f(0) = \lim(f_n(t) - f_n(0)) = \lim\int_0^tf_n' = \int_0^tg$, so $f' = g$. But $D$ is not bounded, since $\|D t^n\|_\infty = n$. So the closed graph theorem needs the completeness of the domain. With the norm $\|f\|_\infty + \|f'\|_\infty$, $C^1[0,1]$ is complete and $D$ has norm $1$.

**Example (Inclusions of sequence spaces).** The inclusion $\ell^1 \to \ell^2$ has $\|x\|_2 \le \|x\|_1$, and it is not surjective. By the corollary on complete norms, $\ell^1$ is not complete for $\|\cdot\|_2$: if it were, the two norms on $\ell^1$ would be equivalent, but $x = (1, \dots, 1, 0, \dots)$ with $N$ ones has $\|x\|_1 = N$ and $\|x\|_2 = \sqrt N$.

### The library around it

The file `Mathlib.Analysis.Normed.Operator.Banach` has the whole sequence of this section, the nonlinear right inverses `ContinuousLinearMap.NonlinearRightInverse`, the equivalence of a closed range and an antilipschitz bound for injective operators (`isClosed_range_iff_antilipschitz_of_injective`), the continuous equivalence onto a closed range `ContinuousLinearMap.equivRange`, and `ContinuousLinearMap.spectrum_eq`, which identifies the spectrum of an operator with the spectrum of its linear map. Open mapping for affine maps is `AffineMap.isOpenMap`.

Common errors of a learner:

- Forgetting one of the two completeness hypotheses.
- Confusing a closed graph with a closed range.
- Expecting a linear right inverse from the open mapping theorem. The theorem gives bounded preimages, and a bounded linear right inverse exists only when the kernel has a closed complement.

### Exercises

1. (A) Show that a continuous map into a Hausdorff space has a closed graph.
2. (A) Show that a linear map $T : E \to F$ is open if and only if $T(B(0, 1))$ contains a ball $B(0, \delta)$.
3. (A) Let $E$ and $F$ be Banach spaces and $T \in L(E, F)$ injective with closed range. Show that $\|x\| \le K\|Tx\|$ for a constant $K$.
4. (B) Let $E$ be a Banach space and $M$, $N$ closed subspaces with $M \cap N = 0$ and $M + N = E$. Show that there is $K$ with $\|m\| + \|n\| \le K\|m + n\|$ for all $m \in M$, $n \in N$.
5. (B) Let $T : E \to E^*$ be linear on a Banach space $E$ with $(Tx)(y) = (Ty)(x)$ for all $x, y$. Show that $T$ is bounded. This is a form of the theorem of Hellinger-Toeplitz.
6. (B) Let $T : \ell^2 \to \ell^2$ be linear and suppose that each coordinate $x \mapsto (Tx)_n$ is continuous. Show that $T$ is bounded.
7. (C) Show that a surjective bounded operator $T : E \to F$ of Banach spaces induces an isomorphism of normed spaces $E / \ker T \to F$.
8. (C) Let $E$ be a Banach space with a countable algebraic (Hamel) basis. Show that $E$ is finite dimensional. Hint: the spans of the first $n$ basis vectors are closed with empty interior.

### Notes and history

The open mapping theorem and the closed graph theorem are in Banach's book of 1932 The open mapping theorem is also attached to the name of Schauder. The theorem of Hellinger and Toeplitz dates from 1910, before the general theory. The file `Mathlib.Analysis.Normed.Operator.Banach` has the author Sébastien Gouëzel.

### Reference

<?reference?>
