---
title: The uniform boundedness principle
kind: theory
modules:
  - Mathlib.Analysis.Normed.Operator.BanachSteinhaus
  - Mathlib.Analysis.LocallyConvex.Barrelled
  - Mathlib.Analysis.Normed.Operator.Completeness
explains:
  E3: [banach_steinhaus, banach_steinhaus_iSup_nnNorm, continuousLinearMapOfTendsto]
  E2: [BarrelledSpace, BaireSpace.instBarrelledSpace, WithSeminorms.banach_steinhaus, NormedSpace.equicontinuous_tfae, ContinuousLinearMap.ofTendstoOfBoundedRange, ContinuousLinearMap.tendsto_of_tendsto_pointwise_of_cauchySeq]
  E1: auto
families: []
requires: [V13, V16.C01, V16.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The uniform boundedness principle

### Overview

Let $(T_i)_{i \in I}$ be a family of bounded operators from a normed space $E$ to a normed space $F$. If the norms $\|T_i\|$ are bounded by $C$, then for each $x$ the vectors $T_ix$ are bounded by $C\|x\|$. The uniform boundedness principle, also called the theorem of Banach-Steinhaus, gives the converse when $E$ is complete: a family that is bounded at each point is bounded in norm. The proof uses the Baire category theorem of Volume 13, which says that a complete metric space is not a countable union of closed sets with empty interior. The principle has two typical uses. It proves that a pointwise limit of bounded operators on a Banach space is bounded. And it proves existence results by contradiction: if a family is not bounded in norm, some single vector makes it unbounded, as for the divergence of Fourier series.

### Definitions

**Definition (Pointwise and uniform bounds).** A family $(T_i)_{i \in I}$ in $L(E, F)$ is *pointwise bounded* if for each $x \in E$ there is $C_x$ with $\|T_ix\| \le C_x$ for all $i$. It is *uniformly bounded* if there is $C$ with $\|T_i\| \le C$ for all $i$.

A uniformly bounded family is pointwise bounded, with $C_x = C\|x\|$. A uniformly bounded family is also *equicontinuous*: for each $\varepsilon > 0$ there is $\delta > 0$ with $\|T_ix - T_iy\| < \varepsilon$ for all $i$ when $\|x - y\| < \delta$.

::: mathlib
`BaireSpace` · `Mathlib.Topology.Defs.Basic`

A topological space is a `BaireSpace` if each countable intersection of dense open sets is dense. Volume 13, Chapter 3, Section 2 proves that a complete metric space is a Baire space. The form used in this section is `nonempty_interior_of_iUnion_of_closed` in `Mathlib.Topology.Baire.Lemmas`: in a nonempty Baire space, if a countable union of closed sets is the whole space, then one of the sets has nonempty interior.

<?decl BaireSpace?>
:::

### Theorems and proofs

**Theorem (Uniform boundedness principle).** Let $E$ be a Banach space, $F$ a normed space, and $(T_i)_{i \in I}$ a pointwise bounded family in $L(E, F)$. Then the family is uniformly bounded.

*Proof.* For $n \in \mathbb{N}$ put
$$A_n = \{x \in E : \|T_ix\| \le n \text{ for all } i \in I\} = \bigcap_{i \in I}\{x : \|T_ix\| \le n\}.$$
Each set $\{x : \|T_ix\| \le n\}$ is closed, as the preimage of $[0, n]$ under the continuous map $x \mapsto \|T_ix\|$, so $A_n$ is closed. Since the family is pointwise bounded, each $x$ lies in $A_n$ for $n \ge C_x$, so $\bigcup_n A_n = E$. The space $E$ is complete, so by the Baire category theorem some $A_N$ has an interior point $x_0$: there is $r > 0$ with $\bar B(x_0, r) \subseteq A_N$.

Let $\|y\| \le r$. Then $x_0 + y$ and $x_0$ lie in $A_N$, so for each $i$,
$$\|T_iy\| = \|T_i(x_0 + y) - T_ix_0\| \le \|T_i(x_0 + y)\| + \|T_ix_0\| \le 2N.$$
For $x \ne 0$ in $E$, the vector $y = rx/\|x\|$ has $\|y\| = r$, so $\|T_ix\| = \frac{\|x\|}{r}\|T_iy\| \le \frac{2N}{r}\|x\|$. So $\|T_i\| \le 2N/r$ for all $i$. $\square$

The proof needs $E$ complete and nothing about $F$. The family can be uncountable: the countability enters only through the sets $A_n$.

::: mathlib
`banach_steinhaus` · `Mathlib.Analysis.Normed.Operator.BanachSteinhaus`

`banach_steinhaus [CompleteSpace E] {g : ι → E →SL[σ₁₂] F} (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) : ∃ C', ∀ i, ‖g i‖ ≤ C'`. The domain `E` is seminormed and complete, and `F` is any seminormed space. The variant `banach_steinhaus_iSup_nnNorm` states the same with suprema in `ℝ≥0∞`: `(∀ x, ⨆ i, ↑‖g i x‖₊ < ∞) → ⨆ i, ↑‖g i‖₊ < ∞`. Its older name `banach_steinhaus_iSup_nnnorm` is deprecated in this edition.

<?decl banach_steinhaus?>
:::

::: mathlib
`banach_steinhaus_iSup_nnNorm` · `Mathlib.Analysis.Normed.Operator.BanachSteinhaus`

The form with suprema is convenient when the bound comes from a limit, since a supremum in `ℝ≥0∞` always exists and the statement needs no witness `C`.

<?decl banach_steinhaus_iSup_nnNorm?>
:::

**Remark (The proof in Mathlib).** Mathlib does not repeat the proof above for normed spaces. It proves the principle for *barrelled* spaces, the topological vector spaces in which each closed absorbing convex balanced set is a neighbourhood of $0$. The class is `BarrelledSpace` in `Mathlib.Analysis.LocallyConvex.Barrelled`, and the instance `BaireSpace.instBarrelledSpace` makes each Baire topological vector space barrelled; the Baire argument of the proof sits in this instance. The general theorem `WithSeminorms.banach_steinhaus` gives equicontinuity of a pointwise bounded family, and `NormedSpace.equicontinuous_tfae` translates equicontinuity of a family of operators into a bound on their norms.

**Corollary (Pointwise limits).** Let $E$ be a Banach space, $F$ a normed space, and $(T_n)$ a sequence in $L(E, F)$ such that $Tx = \lim_n T_nx$ exists for each $x$. Then $T$ is linear and bounded, and
$$\|T\| \le \liminf_{n \to \infty}\|T_n\| < \infty.$$

*Proof.* Linearity follows from the limit of $T_n(ax + by) = aT_nx + bT_ny$. A convergent sequence is bounded, so $(T_n)$ is pointwise bounded, and the principle gives $C$ with $\|T_n\| \le C$ for all $n$. So $L = \liminf\|T_n\|$ is finite. For each $x$, $\|T_nx\| \le \|T_n\|\,\|x\|$, and taking the $\liminf$ of both sides, with the convergence $\|T_nx\| \to \|Tx\|$, gives $\|Tx\| \le L\|x\|$. $\square$

::: mathlib
`continuousLinearMapOfTendsto` · `Mathlib.Analysis.LocallyConvex.Barrelled`

`continuousLinearMapOfTendsto g h : E →SL[σ₁₂] F` from `h : Tendsto (fun n x ↦ g n x) l (𝓝 f)`, the pointwise limit along a countably generated filter `l`, for a barrelled domain `E`. By the instance of the remark it applies to each Banach space. The function of the result is `f`. In `Mathlib.Analysis.Normed.Operator.Completeness` the construction `ContinuousLinearMap.ofTendstoOfBoundedRange` does the same for a family whose norms are bounded by hypothesis, without completeness, and `ContinuousLinearMap.tendsto_of_tendsto_pointwise_of_cauchySeq` gives convergence in norm for a Cauchy sequence.

<?decl continuousLinearMapOfTendsto?>
:::

The corollary does not say that $T_n \to T$ in norm. The coordinate functionals $T_n(x) = x_n$ on $\ell^2$ converge to $0$ at each point, while $\|T_n\| = 1$ for all $n$.

### Examples

**Example (Summing against $c_0$).** Let $(a_n)$ be a sequence of scalars such that $\sum_n a_nx_n$ converges for each $x \in c_0$. Then $(a_n) \in \ell^1$. For the proof put $f_N(x) = \sum_{n \le N}a_nx_n$, a bounded functional on the Banach space $c_0$. Its norm is $\|f_N\| = \sum_{n \le N}|a_n|$: the upper bound is the triangle inequality, and the vector $x$ with $x_n = \overline{\operatorname{sign}(a_n)}$ for $n \le N$ and $x_n = 0$ for $n > N$ has $\|x\|_\infty \le 1$ and $f_N(x) = \sum_{n \le N}|a_n|$. The sequence $f_N(x)$ converges for each $x$, so it is bounded, and the principle gives $\sup_N\sum_{n \le N}|a_n| < \infty$.

**Counterexample (Without completeness).** On $c_{00}$ with $\|\cdot\|_\infty$ let $T_n(x) = n\,x_n$. For each $x \in c_{00}$ only finitely many $x_n$ are nonzero, so $\sup_n|T_nx| < \infty$, and the family is pointwise bounded. But $\|T_n\| = n$, by the vector $e_n$. So the principle fails for the incomplete space $c_{00}$. In the same way the functionals $s_N(x) = \sum_{n \le N}x_n$ converge at each point of $c_{00}$ to the functional $s(x) = \sum_n x_n$, which is not bounded (Chapter 2, Section 1). So the corollary on pointwise limits fails too.

**Example (Fourier series of continuous functions).** Let $C(\mathbb{T})$ be the continuous $2\pi$-periodic functions with $\|\cdot\|_\infty$, a Banach space, and $S_N(f) = \sum_{|k| \le N}\hat f(k)$ the value at $0$ of the partial sum of the Fourier series of $f$. Then $S_N(f) = \frac1{2\pi}\int_{-\pi}^{\pi}f(t)D_N(t)\,dt$ with the Dirichlet kernel $D_N$, and $\|S_N\| = \frac1{2\pi}\int|D_N|$, which tends to $\infty$ like a constant times $\log N$. By the principle, the family $(S_N)$ is not pointwise bounded: some continuous function has a Fourier series that diverges at $0$. The argument gives no formula for the function. The facts about $D_N$ are classical analysis, and the index of this edition has no declaration for the divergence of Fourier series.

**Example (A family on $\ell^1$).** On $\ell^1$ let $T_n(x) = (x_1, 2x_2, \dots, nx_n, 0, 0, \dots)/n$. Then $\|T_nx\|_1 \le \|x\|_1$, so the family is uniformly bounded with $C = 1$, and $T_nx \to 0$ for each $x$ by dominated convergence: the $k$-th coordinate of $T_nx$ is $\frac kn x_k$ for $k \le n$, and $\sum_{k \le n}\frac kn|x_k|$ tends to $0$ by splitting the sum at a fixed $K$. Here the principle is not needed, since the bound is direct. Its value is in the cases where no direct bound is known.

### The library around it

The file `Mathlib.Analysis.Normed.Operator.BanachSteinhaus` has only the two forms of the theorem. The general theory is in `Mathlib.Analysis.LocallyConvex.Barrelled`: `BarrelledSpace`, the principle for families of seminorms, and the continuity of pointwise limits. The Baire category theorem is in `Mathlib.Topology.Baire.Lemmas` and `Mathlib.Topology.Baire.CompleteMetrizable` (Volume 13). The open mapping theorem of the next section uses the Baire theorem in the same way.

Common errors of a learner:

- Applying the principle to a space that is not complete, for example $c_{00}$ or the polynomials.
- Concluding norm convergence from pointwise convergence.
- Forgetting that the principle bounds the norms, not the vectors $T_ix$ uniformly in $x$.

### Exercises

1. (A) Show that the coordinate functionals $x \mapsto x_n$ on $\ell^p$, $1 \le p < \infty$, converge pointwise to $0$ and not in norm.
2. (A) Let $(T_n)$ be a sequence in $L(E, F)$ with $E$ Banach and $\sup_n\|T_nx\| < \infty$ for each $x$. Show that $\sup_n\|T_nx_n\| < \infty$ for each convergent sequence $x_n \to x$.
3. (A) Show that the set $A_n$ in the proof is closed and convex, and that $A_n = -A_n$.
4. (B) Let $(a_n)$ be a sequence with $\sum_na_nx_n$ convergent for each $x \in \ell^1$. Show that $(a_n) \in \ell^\infty$.
5. (B) Let $(a_n)$ be a sequence with $\sum_na_nx_n$ convergent for each $x \in \ell^2$. Show that $(a_n) \in \ell^2$.
6. (B) Let $B : E \times F \to G$ be bilinear with $E$, $F$ Banach, and continuous in each variable when the other one is fixed. Show that $\|B(x, y)\| \le C\|x\|\,\|y\|$ for a constant $C$, so $B$ is continuous.
7. (C) Show that the set of $x \in E$ with $\sup_i\|T_ix\| = \infty$ is either empty or a dense $G_\delta$ subset of $E$, when $E$ is a Banach space.
8. (C) Show that a subset $S$ of a Banach space $E$ is bounded if $f(S)$ is bounded for each $f \in E^*$. Hint: the isometry $E \to E^{**}$ of Chapter 5 and the principle on the Banach space $E^*$.

### Notes and history

The principle is due to Banach and Steinhaus, in a paper in Fundamenta Mathematicae of 1927. A continuous function with a divergent Fourier series was first constructed by du Bois-Reymond in 1873. The file `Mathlib.Analysis.Normed.Operator.BanachSteinhaus` has the author Jireh Loreaux, and the file `Mathlib.Analysis.LocallyConvex.Barrelled` has the author Anatole Dedecker.

### Reference

<?reference?>
