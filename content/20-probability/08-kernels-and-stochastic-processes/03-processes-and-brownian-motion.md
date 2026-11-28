---
title: Processes and Brownian motion
kind: theory
modules:
  - Mathlib.Probability.Kernel.IonescuTulcea.Traj
  - Mathlib.Probability.Process.FiniteDimensionalLaws
  - Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
  - Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def
  - Mathlib.Probability.BrownianMotion.GaussianProjectiveFamily
  - Mathlib.Probability.BrownianMotion.Basic
  - Mathlib.Probability.Kernel.IonescuTulcea.Maps
  - Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
  - Mathlib.Probability.Process.Indistinguishable
  - Mathlib.Probability.Process.Kolmogorov
explains:
  E3: [ProbabilityTheory.Kernel.traj, ProbabilityTheory.Kernel.trajMeasure, ProbabilityTheory.HasIndepIncrements, ProbabilityTheory.IsGaussianProcess, ProbabilityTheory.IsPreBrownianReal, ProbabilityTheory.IsBrownianReal]
  E2: [ProbabilityTheory.Kernel.partialTraj, ProbabilityTheory.Kernel.traj_map_frestrictLe, ProbabilityTheory.Kernel.condDistrib_trajMeasure, ProbabilityTheory.isProjectiveLimit_map, ProbabilityTheory.BrownianReal.projectiveFamily, ProbabilityTheory.BrownianReal.isProjectiveMeasureFamily_projectiveFamily, ProbabilityTheory.IsPreBrownianReal.isGaussianProcess, ProbabilityTheory.IsPreBrownianReal.hasIndepIncrements, ProbabilityTheory.IsPreBrownianReal.hasLaw_sub, ProbabilityTheory.IsPreBrownianReal.covariance_eval, ProbabilityTheory.IsPreBrownianReal.smul, ProbabilityTheory.HasIndepIncrements.isPreBrownianReal_of_hasLaw, ProbabilityTheory.IsBrownianReal.cont, ProbabilityTheory.IsBrownianReal.shift, ProbabilityTheory.IsBrownianReal.tendsto_nhds_zero]
  E1: auto
families: []
requires: [V03, V13, V15, V20.C01, V20.C02, V20.C03, V20.C04, V20.C05, V20.C06, V20.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Processes and Brownian motion

### Overview

A stochastic process is a family $(X_t)_{t \in T}$ of random variables on one probability space. Its law is a measure on the path space $\prod_t E_t$, and it is fixed by the finite-dimensional laws, the laws of the vectors $(X_{t_1}, \ldots, X_{t_n})$. This section constructs processes in discrete time from kernels with the Ionescu-Tulcea theorem, and gives the definitions of Gaussian processes, processes with independent increments and Brownian motion as Mathlib has them.

### Definitions

**Definition (Trajectory measure).** Let $(E_n)_{n \in \mathbb{N}}$ be measurable spaces, let $\mu_0$ be a probability measure on $E_0$, and for each $n$ let $\kappa_n$ be a Markov kernel from $E_0 \times \cdots \times E_n$ to $E_{n+1}$. A *trajectory measure* is a probability measure $P$ on $\prod_n E_n$ under which the coordinate $X_0$ has the law $\mu_0$, and the conditional law of $X_{n+1}$ given $(X_0, \ldots, X_n)$ is $\kappa_n$.

::: mathlib
`ProbabilityTheory.Kernel.traj` · `Mathlib.Probability.Kernel.IonescuTulcea.Traj`

`traj κ a` is the Ionescu-Tulcea kernel: from a path up to time `a`, it gives the law of the whole path. `partialTraj κ a b` is the kernel from the path up to time `a` to the path up to time `b`, a finite composition-product of the `κ n`. `traj_map_frestrictLe` says that the restriction of `traj κ a` to the times up to `b` is `partialTraj κ a b`.

<?decl ProbabilityTheory.Kernel.traj?>
:::

::: mathlib
`ProbabilityTheory.Kernel.trajMeasure` · `Mathlib.Probability.Kernel.IonescuTulcea.Traj`

`trajMeasure μ₀ κ` is the trajectory measure with the initial law `μ₀`. `condDistrib_trajMeasure` says that the conditional distribution of the coordinate `a + 1` given the path up to time `a` is `κ a`, a.e.

<?decl ProbabilityTheory.Kernel.trajMeasure?>
:::

**Definition (Independent increments).** A process $(X_t)_{t \in T}$ on an ordered set $T$ has *independent increments* if $X_{t_2} - X_{t_1}, \ldots, X_{t_n} - X_{t_{n-1}}$ are independent for all $t_1 \le \cdots \le t_n$.

::: mathlib
`ProbabilityTheory.HasIndepIncrements` · `Mathlib.Probability.Process.HasIndepIncrements.Basic`

`HasIndepIncrements X P` states the definition with `iIndepFun` of Chapter 2, for a family indexed by `Fin n`.

<?decl ProbabilityTheory.HasIndepIncrements?>
:::

**Definition (Gaussian process).** A real process is *Gaussian* if each finite-dimensional law is Gaussian, in the sense of Chapter 4.

::: mathlib
`ProbabilityTheory.IsGaussianProcess` · `Mathlib.Probability.Process.IsGaussianProcess.Def`

`IsGaussianProcess X P` asks that each restriction of the process to a finite set of times has a Gaussian law, with `HasGaussianLaw` of Chapter 4. The values can be in a topological vector space.

<?decl ProbabilityTheory.IsGaussianProcess?>
:::

**Definition (Brownian motion).** A real process $(B_t)_{t \ge 0}$ is a *pre-Brownian motion* if it is a centred Gaussian process with $\operatorname{Cov}(B_s, B_t) = \min(s, t)$. It is a *Brownian motion* if also its paths $t \mapsto B_t(\omega)$ are continuous for a.e. $\omega$.

::: mathlib
`ProbabilityTheory.IsPreBrownianReal` · `Mathlib.Probability.BrownianMotion.Basic`

`IsPreBrownianReal B P`, for `B : ℝ≥0 → Ω → ℝ`, says that the finite-dimensional laws of `B` are the measures `BrownianReal.projectiveFamily I`. Each of them is the centred Gaussian law on `I → ℝ` with the covariance matrix $\min(s, t)$, and they form a projective family (`BrownianReal.isProjectiveMeasureFamily_projectiveFamily`). The consequences are `IsPreBrownianReal.isGaussianProcess`, `IsPreBrownianReal.hasIndepIncrements`, `IsPreBrownianReal.hasLaw_sub` ($B_s - B_t \sim \mathcal{N}(0, |s - t|)$) and `IsPreBrownianReal.covariance_eval`. The converse `HasIndepIncrements.isPreBrownianReal_of_hasLaw` starts from independent increments and the laws $B_t \sim \mathcal{N}(0, t)$.

<?decl ProbabilityTheory.IsPreBrownianReal?>
:::

::: mathlib
`ProbabilityTheory.IsBrownianReal` · `Mathlib.Probability.BrownianMotion.Basic`

`IsBrownianReal B P` adds the a.s. continuity of the paths, which `IsBrownianReal.cont` extracts. `IsBrownianReal.shift` says that $t \mapsto B_{t_0 + t} - B_{t_0}$ is a Brownian motion. `IsBrownianReal.tendsto_nhds_zero` says that a.s. $B_t \to 0$ as $t \to 0$.

<?decl ProbabilityTheory.IsBrownianReal?>
:::

### Theorems and proofs

**Theorem (Ionescu-Tulcea).** Under the hypotheses of the first definition, there is a unique trajectory measure.

*Proof sketch.* The finite composition-products $\mu_0 \otimes \kappa_0 \otimes \cdots \otimes \kappa_{n-1}$ of Section 1 are probability measures $P_n$ on $E_0 \times \cdots \times E_n$, and they are consistent: $P_{n+1}$ restricts to $P_n$. They define an additive set function $P$ on the algebra of cylinder sets. By the Carathéodory extension theorem of Volume 18, it is enough to prove that $P(C_k) \to 0$ for each decreasing sequence of cylinders with $\bigcap_k C_k = \varnothing$. If $P(C_k) \ge \varepsilon > 0$ for all $k$, the integrals $x_0 \mapsto \operatorname{traj}(x_0)(C_k)$ give a point $x_0$ with $\inf_k \kappa$-probability $\ge \varepsilon$, and an induction gives a path $(x_0, x_1, \ldots)$ in each $C_k$, which is a contradiction. No topology on the $E_n$ is necessary. $\square$

**Theorem (Finite-dimensional laws fix the law).** Two processes with the same finite-dimensional laws have the same law on $\prod_t E_t$.

*Proof.* The cylinder sets form a $\pi$-system that generates the product $\sigma$-algebra, and the two laws agree on it. $\square$

In Mathlib, `isProjectiveLimit_map` says that the law of a process is the projective limit of its finite-dimensional laws.

**Theorem (Scaling).** If $B$ is a pre-Brownian motion and $c > 0$, then $t \mapsto c^{-1/2} B_{ct}$ is a pre-Brownian motion.

*Proof.* The process is centred Gaussian, as a linear image of $B$, and $\operatorname{Cov}(c^{-1/2}B_{cs}, c^{-1/2}B_{ct}) = c^{-1}\min(cs, ct) = \min(s, t)$. $\square$

In Mathlib this is `IsPreBrownianReal.smul`.

### Examples

**Example (A Markov chain).** For a Markov kernel $\kappa$ on $E$, let $\kappa_n(x_0, \ldots, x_n) = \kappa(x_n)$. Then `trajMeasure μ₀ κ` is the law of the Markov chain with transition kernel $\kappa$ and initial law $\mu_0$. With the two-state kernel of Section 1, it is the law of the machine of that example over all days.

**Example (Brownian motion as a limit of walks).** Let $S_n$ be the simple random walk and let $W^{(n)}_t = S_{\lfloor nt \rfloor} / \sqrt{n}$. For fixed $s < t$, the central limit theorem of Chapter 5 gives $W^{(n)}_t - W^{(n)}_s \to \mathcal{N}(0, t - s)$ in distribution, and the increments over disjoint intervals are independent. So the finite-dimensional laws of $W^{(n)}$ converge to those of a pre-Brownian motion.

**Counterexample (Finite-dimensional laws do not fix the paths).** Let $B$ be a Brownian motion and let $U$ be uniform on $[0, 1]$ and independent of $B$. Let $\tilde{B}_t = B_t + \mathbf{1}_{\{t = U\}}$. For each fixed $t$, $\tilde{B}_t = B_t$ a.s., so $\tilde{B}$ has the finite-dimensional laws of $B$, and it is a pre-Brownian motion. But no path of $\tilde{B}$ is continuous. Continuity is a property of a version of the process, and not of its law on the product $\sigma$-algebra.

### The library around it

The Ionescu-Tulcea construction is in `Mathlib/Probability/Kernel/IonescuTulcea/`. The Kolmogorov continuity condition is in `Mathlib/Probability/Process/Kolmogorov.lean`, as the predicate `IsKolmogorovProcess` on the moments $E[d(X_s, X_t)^p] \le M\, d(s, t)^q$. The index of this edition has no declaration for the Kolmogorov extension theorem on an uncountable product of Polish spaces, nor for the existence of a Brownian motion.

The first step of the construction is in `Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj`. For kernels $\kappa_n$ from the paths up to time $n$ to the state at time $n + 1$, the kernel `ProbabilityTheory.Kernel.partialTraj` $\kappa$ $a$ $b$ goes from the paths up to time $a$ to the paths up to time $b$. It applies $\kappa_a, \dots, \kappa_{b - 1}$ in turn and keeps the past, and for $b \le a$ it only restricts the path. The theorem `ProbabilityTheory.Kernel.partialTraj_comp_partialTraj` gives the composition law $\mathrm{partialTraj}(b, c) \circ \mathrm{partialTraj}(a, b) = \mathrm{partialTraj}(a, c)$ for $a \le b \le c$, and `ProbabilityTheory.Kernel.partialTraj_succ_eq_comp` gives one step. The function `ProbabilityTheory.Kernel.lmarginalPartialTraj` integrates a function of the whole path against the partial trajectory, and its lemmas give the projective property that the theorem of Ionescu-Tulcea needs. The module `Mathlib.Probability.Kernel.IonescuTulcea.Maps` provides the measurable bijections that glue path pieces, such as `MeasurableEquiv.IicProdIoc`, which identifies a path up to $a$ and a path on $(a, b]$ with a path up to $b$, and `MeasurableEquiv.IicProdIoi`.

The module `Mathlib.Probability.Process.Indistinguishable` defines `ProbabilityTheory.Indistinguishable` $P$ $X$ $Y$, with the notation `X ≡ᵐ[P] Y`. It says that almost surely $X_t = Y_t$ for all $t$ at once. This is stronger than a modification, where for each $t$ the equality holds almost surely, with a null set that depends on $t$. The two notions agree for a countable index set, and for continuous processes on $\mathbb{R}$. The predicate is an equivalence relation, by `ProbabilityTheory.Indistinguishable.refl` and `ProbabilityTheory.Indistinguishable.trans`, and it is compatible with sums, products, scalars and composition, for example `ProbabilityTheory.Indistinguishable.add` and `ProbabilityTheory.Indistinguishable.fun_comp`. The lemma `ProbabilityTheory.Indistinguishable.ae_eq_eval` gives the modification at each $t$.

The module `Mathlib.Probability.Process.Kolmogorov` defines the condition of the Kolmogorov continuity theorem. The structure `ProbabilityTheory.IsKolmogorovProcess` $X$ $P$ $p$ $q$ $M$ asks that each pair $(X_s, X_t)$ is measurable, that $p, q > 0$, and that $E[d(X_s, X_t)^p] \le M \, d(s, t)^q$. The predicate `ProbabilityTheory.IsAEKolmogorovProcess` says that $X$ is a modification of such a process, and `ProbabilityTheory.IsAEKolmogorovProcess.mk` chooses this process. The theorem `ProbabilityTheory.IsKolmogorovProcess.edist_eq_zero` says that the distance between $X_s$ and $X_t$ is $0$ almost surely when $d(s, t) = 0$. The pre-Brownian motion satisfies the condition, since $E[|B_t - B_s|^{2n}] = c_n |t - s|^n$.

### Exercises

1. (A) Prove that a pre-Brownian motion has $B_0 = 0$ a.s. and $E[(B_t - B_s)^2] = |t - s|$.
2. (A) Prove that $-B$ and $B_{t_0 + t} - B_{t_0}$ are pre-Brownian motions.
3. (B) Prove that a Brownian motion $B$ is a martingale for its natural filtration, and that $B_t^2 - t$ is a martingale too.
4. (B) Prove that a centred Gaussian process with independent increments and $\operatorname{Var}(B_t) = t$ has the covariance $\min(s, t)$.
5. (B) Prove that $t B_{1/t}$, with the value $0$ at $t = 0$, is a pre-Brownian motion.
6. (C) Prove that the paths of a Brownian motion are a.s. not of bounded variation on $[0, 1]$. Use $\sum_k (B_{k/n} - B_{(k-1)/n})^2 \to 1$ in $L^2$.

### Notes and history

Ionescu Tulcea proved his theorem in 1949. Kolmogorov proved the extension theorem in his *Grundbegriffe* of 1933. Wiener constructed Brownian motion as a measure on continuous paths in 1923. Bachelier used it in 1900 in his thesis on the prices of shares, and Einstein in 1905 for the motion of particles in a fluid.

### Reference

<?reference?>
