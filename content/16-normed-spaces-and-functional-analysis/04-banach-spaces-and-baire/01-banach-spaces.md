---
title: Banach spaces, quotients and completions
kind: theory
modules:
  - Mathlib.Analysis.Normed.Group.Quotient
  - Mathlib.Analysis.Normed.Group.Completion
  - Mathlib.Analysis.Normed.Module.Completion
  - Mathlib.Analysis.Hofer
explains:
  E3: [QuotientAddGroup.norm_mk, QuotientAddGroup.instNormedAddCommGroup, Submodule.Quotient.completeSpace, UniformSpace.Completion.toComplₗᵢ]
  E2: [QuotientAddGroup.norm_mk_eq_zero_iff_mem_closure, Submodule.Quotient.norm_mk_lt, Submodule.Quotient.norm_mk_le, Submodule.Quotient.normedSpace, Submodule.Quotient.normedAddCommGroup, UniformSpace.Completion.norm_coe, UniformSpace.Completion.instNormedAddCommGroup, UniformSpace.Completion.instNormedSpace]
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

## Banach spaces, quotients and completions

### Overview

The spaces $\ell^p$, $C[0,1]$ and $L(E, F)$ with $F$ complete are complete, and the space $c_{00}$ of finitely supported sequences is not. The complete normed spaces are the *Banach spaces*, and the theorems of the next two sections hold only for them. This section gives the three standard ways to make new Banach spaces from old ones. A closed subspace of a Banach space is a Banach space. The quotient of a Banach space by a closed subspace, with the quotient norm, is a Banach space. Each normed space is a dense subspace of a Banach space, its completion. The examples show a subspace of $C[0,1]$ that is not closed, the quotient $\ell^\infty / c_0$, and the completion of $c_{00}$.

### Definitions

**Definition (Banach space).** A *Banach space* is a normed space that is complete for the metric $d(x, y) = \|x - y\|$.

::: mathlib
`CompleteSpace` · `Mathlib.Topology.UniformSpace.Cauchy`

Mathlib has no class for Banach spaces. A real Banach space is written `[NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]`, where `CompleteSpace E` is the class of complete uniform spaces of Volume 13: each Cauchy filter converges. Since completeness is a separate class, each theorem states exactly where it needs it. For example the uniform boundedness principle needs `CompleteSpace E` for the domain only, and the open mapping theorem needs it for both spaces.

<?decl CompleteSpace?>
:::

**Definition (Quotient norm).** Let $M$ be a subspace of a normed space $E$ and $\pi : E \to E/M$ the quotient map. For $\xi = \pi(x)$ put
$$\|\xi\| = \inf_{y \in M}\|x - y\| = d(x, M).$$

The value does not depend on the choice of $x$: if $\pi(x) = \pi(x')$, then $x' - x \in M$ and $\{x' - y : y \in M\} = \{x - y : y \in M\}$.

::: mathlib
`QuotientAddGroup.norm_mk` · `Mathlib.Analysis.Normed.Group.Quotient`

`‖(x : M ⧸ S)‖ = Metric.infDist x S` for an additive subgroup `S` of a seminormed group `M`. The quotient is a seminormed group for each `S`. For a submodule `S` the quotient `M ⧸ S` is the same type with the instances `Submodule.Quotient.seminormedAddCommGroup` and `Submodule.Quotient.normedSpace`. The two lemmas used most are `Submodule.Quotient.norm_mk_le : ‖mk m‖ ≤ ‖m‖` and `Submodule.Quotient.norm_mk_lt`, which lifts an element of the quotient to a vector of norm less than `‖x‖ + ε`.

<?decl QuotientAddGroup.norm_mk?>
:::

**Definition (Completion).** A *completion* of a normed space $E$ is a Banach space $\hat E$ with a linear isometry $\iota : E \to \hat E$ whose image is dense.

### Theorems and proofs

**Theorem (Closed subspaces).** Let $E$ be a Banach space and $M$ a subspace. Then $M$ with the norm of $E$ is a Banach space if and only if $M$ is closed in $E$.

*Proof.* If $M$ is closed and $(x_n)$ is a Cauchy sequence in $M$, it is Cauchy in $E$, so it has a limit $x \in E$, and $x \in M$ since $M$ is closed. Conversely, if $M$ is complete and $x$ is in the closure of $M$, there are $x_n \in M$ with $x_n \to x$. The sequence $(x_n)$ is Cauchy, so it has a limit in $M$, which is $x$ by the uniqueness of limits. $\square$

The first half needs the completeness of $E$, and the second half holds in each metric space (Volume 13). In Mathlib the two halves are `IsClosed.completeSpace_coe` and `IsComplete.isClosed`. The closure $\overline M$ of a subspace is a subspace, `Submodule.topologicalClosure` in `Mathlib.Topology.Algebra.Module.Basic`, so the closure of a subspace of a Banach space is a Banach space.

**Theorem (The quotient norm).** Let $M$ be a subspace of a normed space $E$.

1. The quotient norm is a seminorm on $E/M$, and $\|\pi(x)\| \le \|x\|$.
2. $\|\pi(x)\| = 0$ if and only if $x \in \overline M$. So the quotient norm is a norm if and only if $M$ is closed.
3. For $\xi \in E/M$ and $\varepsilon > 0$ there is $x$ with $\pi(x) = \xi$ and $\|x\| < \|\xi\| + \varepsilon$.

*Proof.* (3) is the definition of the infimum. For (1), $y = 0$ gives $\|\pi(x)\| \le \|x\|$. For the triangle inequality, let $\xi, \eta \in E/M$ and $\varepsilon > 0$, and choose lifts $x, x'$ by (3). Then $\pi(x + x') = \xi + \eta$, so $\|\xi + \eta\| \le \|x + x'\| < \|\xi\| + \|\eta\| + 2\varepsilon$. Homogeneity: for $c \neq 0$, $\{cx - y : y \in M\} = c\{x - y : y \in M\}$, so $\|c\xi\| = |c|\,\|\xi\|$. For (2), $d(x, M) = 0$ means that $x$ is a limit of points of $M$. $\square$

::: mathlib
`QuotientAddGroup.instNormedAddCommGroup` · `Mathlib.Analysis.Normed.Group.Quotient`

The instance `NormedAddCommGroup (M ⧸ S)` from a hypothesis `[hS : IsClosed (S : Set M)]`. It needs this instance argument, so in a proof one writes `haveI : IsClosed (S : Set M) := h` first. Part (2) is `QuotientAddGroup.norm_mk_eq_zero_iff_mem_closure`. For submodules the normed group instance is `Submodule.Quotient.normedAddCommGroup`.

<?decl QuotientAddGroup.instNormedAddCommGroup?>
:::

**Theorem (Quotients of Banach spaces).** Let $E$ be a Banach space and $M$ a closed subspace. Then $E/M$ with the quotient norm is a Banach space.

*Proof.* By the criterion of Chapter 1, Section 3, it suffices to show that each absolutely convergent series in $E/M$ converges. Let $\sum_n\|\xi_n\| < \infty$. By part (3) of the last theorem choose $x_n$ with $\pi(x_n) = \xi_n$ and $\|x_n\| < \|\xi_n\| + 2^{-n}$. Then $\sum_n\|x_n\| < \sum_n\|\xi_n\| + 1 < \infty$, so $\sum_n x_n$ converges in the Banach space $E$, to a vector $x$. Since $\pi$ is linear with $\|\pi(z)\| \le \|z\|$, it is continuous, so
$$\pi(x) = \lim_N \pi\Big(\sum_{n \le N}x_n\Big) = \lim_N\sum_{n \le N}\xi_n.$$
So $\sum_n\xi_n$ converges to $\pi(x)$. $\square$

::: mathlib
`Submodule.Quotient.completeSpace` · `Mathlib.Analysis.Normed.Group.Quotient`

The instance `CompleteSpace (M ⧸ S)` for each submodule `S` of a complete seminormed group `M`. It needs no closedness: for `S` not closed the quotient is a complete seminormed space. The Mathlib proof does not use series. It transfers the completeness of the quotient of a complete topological group by a subgroup, `QuotientAddGroup.completeSpace_left`, from the topological algebra of Volume 14.

<?decl Submodule.Quotient.completeSpace?>
:::

**Theorem (Completion).** Each normed space $E$ has a completion $\hat E$. If $(\hat E, \iota)$ and $(\hat E', \iota')$ are two completions, there is a unique linear isometric equivalence $\varphi : \hat E \to \hat E'$ with $\varphi \circ \iota = \iota'$.

*Proof.* Volume 13 builds the completion $\hat E$ of $E$ as a uniform space, with a uniformly continuous map $\iota : E \to \hat E$ whose image is dense, and proves that each uniformly continuous map $E \to Y$ into a complete space extends uniquely to $\hat E$. Addition $E \times E \to E$ and multiplication by a scalar $c$ are uniformly continuous, so they extend to $\hat E$. The vector space identities hold on the dense set $\iota(E)$, and both sides are continuous, so they hold on $\hat E$. In the same way the norm $E \to \mathbb{R}$ is uniformly continuous and extends to $\hat E$. The axioms of a norm, including $\|cx\| = |c|\,\|x\|$ and the identity $d(\xi, \eta) = \|\xi - \eta\|$, are closed conditions that hold on $\iota(E)$, so they hold on $\hat E$. For the uniqueness, $\iota' \circ \iota^{-1}$ is an isometry from the dense subspace $\iota(E)$ into the complete space $\hat E'$, so it extends uniquely to a linear isometry $\varphi$, and its image is closed and dense, hence all of $\hat E'$. $\square$

::: mathlib
`UniformSpace.Completion.toComplₗᵢ` · `Mathlib.Analysis.Normed.Module.Completion`

`toComplₗᵢ : E →ₗᵢ[𝕜] UniformSpace.Completion E`, the embedding of a seminormed space into its completion as a linear isometry. The normed structure on the completion is the instance `UniformSpace.Completion.instNormedAddCommGroup` in `Mathlib.Analysis.Normed.Group.Completion`, with `UniformSpace.Completion.norm_coe : ‖(x : Completion E)‖ = ‖x‖`, and the scalars come from `UniformSpace.Completion.instNormedSpace`. The density of the image is `UniformSpace.Completion.denseRange_coe` of Volume 13.

<?decl UniformSpace.Completion.toComplₗᵢ?>
:::

### Examples

**Example (The sequence space $c_0$).** The space $c_0$ of sequences with limit $0$ is closed in $\ell^\infty$ (Chapter 1, Section 3, Exercise 5), so it is a Banach space by the theorem on closed subspaces. The subspace $c_{00}$ is dense in $c_0$, and $c_0$ with the inclusion is the completion of $c_{00}$, by the uniqueness of completions. In the same way the completion of $c_{00}$ with $\|\cdot\|_p$ for $1 \le p < \infty$ is $\ell^p$.

**Counterexample (The polynomials in $C[0,1]$).** Let $P \subseteq C[0,1]$ be the polynomial functions, with $\|\cdot\|_\infty$. The theorem of Weierstrass (`polynomialFunctions_closure_eq_top'` in `Mathlib.Topology.ContinuousMap.Weierstrass`) says that $P$ is dense in $C[0,1]$. The function $t \mapsto |t - \frac12|$ is in $C[0,1]$ and it is not a polynomial, since it is not differentiable at $\frac12$. So $P \ne C[0,1]$, and $P$ is not closed and not complete. Concretely, the Taylor polynomials $p_N(t) = \sum_{k \le N}t^k/k!$ form a Cauchy sequence in $P$ with $\|p_N - e^t\|_\infty \le \sum_{k > N}1/k! \to 0$, and the limit $e^t$ is not a polynomial, since each derivative of it is nonzero. The completion of $P$ is $C[0,1]$.

**Example (The quotient $\ell^\infty / c_0$).** For $x \in \ell^\infty$ the quotient norm is $\|\pi(x)\| = \limsup_n|x_n|$. Upper bound: for $\varepsilon > 0$ there is $N$ with $|x_n| \le \limsup|x_k| + \varepsilon$ for $n \ge N$. The vector $y$ with $y_n = x_n$ for $n < N$ and $y_n = 0$ for $n \ge N$ lies in $c_0$, and $\|x - y\|_\infty \le \limsup|x_k| + \varepsilon$. Lower bound: for $y \in c_0$, $\|x - y\|_\infty \ge \limsup_n|x_n - y_n| = \limsup_n|x_n|$. For $x = (1, 0, 1, 0, \dots)$ the quotient norm is $1$, and for $x = (1/n)$ it is $0$, which agrees with $x \in c_0$.

**Example (A quotient of $\mathbb{R}^3$).** Let $E = \mathbb{R}^3$ with $\|\cdot\|_1$ and $M = \mathbb{R}(1, 1, 1)$. For $x = (2, 0, 0)$, $\|\pi(x)\| = \min_t(|2 - t| + 2|t|)$. The function is $2 + t$ for $t \in [0, 2]$ and $2 - 3t$ for $t \le 0$, so its minimum is $2$, at $t = 0$. So $\|\pi(x)\| = 2 = \|x\|_1$. For $x = (1, 1, 0)$, $\min_t(2|1 - t| + |t|) = 1$, at $t = 1$, while $\|x\|_1 = 2$.

### The library around it

The file `Mathlib.Analysis.Normed.Group.Quotient` has the quotient norm for groups, modules and ideals, the normed group map $\pi$ as `AddSubgroup.normedMk` with `AddSubgroup.norm_normedMk_le`, the lift of a normed group map that vanishes on $M$ as `NormedAddGroupHom.lift`, and the quotient rings `Ideal.Quotient.normedCommRing`. The files `Mathlib.Analysis.Normed.Group.Completion` and `Mathlib.Analysis.Normed.Module.Completion` put the normed structure on `UniformSpace.Completion E`, including the normed ring and the normed algebra structures. The extension of a bounded operator from a dense subspace to the completion, with the same norm, is `ContinuousLinearMap.extend` with `ContinuousLinearMap.opNorm_extend_le` in `Mathlib.Analysis.Normed.Operator.Extend`.

The file `Mathlib.Analysis.Hofer` proves a lemma of Hofer on complete metric spaces, the theorem `hofer`. Let $\varphi \ge 0$ be continuous on a complete metric space $X$, let $x \in X$ and $\varepsilon > 0$. Then there are $0 < \varepsilon' \le \varepsilon$ and $x'$ with $d(x', x) \le 2 \varepsilon$ and $\varepsilon \varphi(x) \le \varepsilon' \varphi(x')$, such that $\varphi(y) \le 2 \varphi(x')$ for all $y$ with $d(x', y) \le \varepsilon'$. The proof is an iteration in the style of the theorem of Baire: if a point fails, move to a nearby point where $\varphi$ doubles and halve the radius. If this never stops, the points form a Cauchy sequence, and $\varphi$ is unbounded near its limit, which contradicts continuity.

Common errors of a learner:

- Writing `CompleteSpace` for a subspace `M` and forgetting that the instance on `↥M` needs `IsClosed`, given with `haveI`.
- Using the quotient norm of a subspace that is not closed and expecting a norm. For a dense $M$ the quotient norm is $0$.
- Expecting a closed subspace of a Banach space to have a closed complement. In $\ell^\infty$ the subspace $c_0$ has none, by a theorem of Phillips.

### Exercises

1. (A) Show that the space of convergent sequences $c$ is a closed subspace of $\ell^\infty$, and that $c_0$ is a closed subspace of $c$ with $c/c_0$ isometric to $\mathbb{R}$ by $\pi(x) \mapsto \lim x_n$.
2. (A) In $\mathbb{R}^2$ with $\|\cdot\|_\infty$ and $M = \mathbb{R}(1, 1)$, compute $\|\pi(x_1, x_2)\|$.
3. (A) Show that the quotient map $\pi : E \to E/M$ has $\|\pi\| = 1$ when $M$ is a closed subspace with $M \ne E$. Hint: the lemma of Riesz.
4. (B) Show that $\pi$ maps the open unit ball of $E$ onto the open unit ball of $E/M$.
5. (B) Show that $\{f \in C[0,1] : f(0) = 0\}$ is closed and that the quotient $C[0,1] / \{f : f(0) = 0\}$ is isometric to $\mathbb{R}$.
6. (B) Show that the space of Lipschitz functions $f$ on $[0,1]$ with $f(0) = 0$ is not closed in $C[0,1]$. Find its closure.
7. (C) Let $E$ be a normed space and $M$ a closed subspace. Show that if $M$ and $E/M$ are complete, then $E$ is complete.
8. (C) Let $T : E \to F$ be a bounded operator and $M$ a closed subspace with $M \subseteq \ker T$. Show that there is a unique bounded $\tilde T : E/M \to F$ with $\tilde T \circ \pi = T$, and that $\|\tilde T\| = \|T\|$.

### Notes and history

The name "Banach space" honours Stefan Banach, whose thesis of 1920, published in 1922, gave the axioms of a complete normed space. The theorem of Phillips that $c_0$ has no closed complement in $\ell^\infty$ dates from 1940. The file `Mathlib.Analysis.Normed.Group.Quotient` has the authors Patrick Massot and Riccardo Brasca, and the file `Mathlib.Analysis.Normed.Module.Completion` has the author Yury Kudryashov.

### Reference

<?reference?>
