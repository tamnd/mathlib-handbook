---
title: Markov kernels
kind: theory
modules:
  - Mathlib.Probability.Kernel.Defs
  - Mathlib.Probability.Kernel.Basic
  - Mathlib.Probability.Kernel.Composition.Comp
  - Mathlib.Probability.Kernel.Composition.CompProd
  - Mathlib.Probability.Kernel.Composition.MeasureCompProd
  - Mathlib.Probability.Kernel.Composition.Prod
  - Mathlib.Probability.Kernel.Composition.MapComap
  - Mathlib.Probability.Kernel.Composition.CompMap
  - Mathlib.Probability.Kernel.Invariance
  - Mathlib.Probability.Kernel.Irreducible
explains:
  E3: [ProbabilityTheory.Kernel, ProbabilityTheory.IsMarkovKernel, ProbabilityTheory.Kernel.comp, ProbabilityTheory.Kernel.compProd, MeasureTheory.Measure.compProd, ProbabilityTheory.Kernel.Invariant]
  E2: [ProbabilityTheory.IsFiniteKernel, ProbabilityTheory.IsSFiniteKernel, ProbabilityTheory.Kernel.measurable_coe, ProbabilityTheory.Kernel.ext, ProbabilityTheory.Kernel.deterministic, ProbabilityTheory.Kernel.deterministic_apply, ProbabilityTheory.Kernel.const, ProbabilityTheory.Kernel.const_apply, ProbabilityTheory.Kernel.id, ProbabilityTheory.Kernel.comp_apply, ProbabilityTheory.Kernel.lintegral_comp, ProbabilityTheory.Kernel.comp_assoc, ProbabilityTheory.Kernel.comp_id, ProbabilityTheory.Kernel.id_comp, ProbabilityTheory.Kernel.compProd_apply, ProbabilityTheory.Kernel.lintegral_compProd, MeasureTheory.Measure.compProd_apply, ProbabilityTheory.Kernel.prod, ProbabilityTheory.Kernel.prod_apply, ProbabilityTheory.Kernel.map, ProbabilityTheory.Kernel.map_apply, ProbabilityTheory.Kernel.comap, ProbabilityTheory.Kernel.fst, ProbabilityTheory.Kernel.snd, ProbabilityTheory.Kernel.prodMkLeft, ProbabilityTheory.Kernel.deterministic_comp_eq_map, ProbabilityTheory.Kernel.comp_deterministic_eq_comap, ProbabilityTheory.Kernel.Invariant.def, ProbabilityTheory.Kernel.Invariant.comp]
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

## Markov kernels

### Overview

A Markov kernel from $X$ to $Y$ is a measurable family of probability measures on $Y$, one for each point of $X$. It is the measure theoretic form of a random transition: the law of the next state, given the present state. Kernels compose like matrices, a measure and a kernel give a joint law on a product space, and a measure that a kernel does not change is a stationary law. Mathlib uses kernels as a basic language of its probability library: independence, conditional distributions and the construction of processes are all stated with kernels. This section gives the definitions and the operations.

### Definitions

**Definition (Kernel).** Let $(X, \mathcal{A})$ and $(Y, \mathcal{B})$ be measurable spaces. A *kernel* from $X$ to $Y$ is a map $\kappa : X \to \mathcal{M}(Y)$ into the measures on $Y$ such that $x \mapsto \kappa(x)(B)$ is measurable for each $B \in \mathcal{B}$. It is a *Markov kernel* if each $\kappa(x)$ is a probability measure, and a *finite kernel* if $\sup_x \kappa(x)(Y) < \infty$. It is *s-finite* if it is a countable sum of finite kernels.

::: mathlib
`ProbabilityTheory.Kernel` · `Mathlib.Probability.Kernel.Defs`

`Kernel α β` is a structure with a function `α → Measure β` that is measurable for the Giry σ-algebra on `Measure β`. It coerces to a function, `κ a` is a measure, and `Kernel.measurable_coe` gives the measurability of `a ↦ κ a s`. `Kernel.ext` is extensionality. The classes `IsMarkovKernel`, `IsFiniteKernel` and `IsSFiniteKernel` are the three properties. Many results of the library need s-finite kernels, because the Fubini theorems of Volume 18, Measure and integration, need s-finite measures.

<?decl ProbabilityTheory.Kernel?>
:::

::: mathlib
`ProbabilityTheory.IsMarkovKernel` · `Mathlib.Probability.Kernel.Defs`

`IsMarkovKernel κ` asks `∀ a, IsProbabilityMeasure (κ a)`. Instances give the property for the basic kernels and the operations below, so the type class system proves it in most cases.

<?decl ProbabilityTheory.IsMarkovKernel?>
:::

The basic kernels are the following. The *deterministic kernel* of a measurable map $f : X \to Y$ is $x \mapsto \delta_{f(x)}$ (`Kernel.deterministic f hf`, with `Kernel.deterministic_apply`). The *identity kernel* is $x \mapsto \delta_x$ (`Kernel.id`). The *constant kernel* of a measure $\mu$ on $Y$ is $x \mapsto \mu$ (`Kernel.const`, with `Kernel.const_apply`).

**Definition (Composition).** For a kernel $\kappa$ from $X$ to $Y$ and a kernel $\eta$ from $Y$ to $Z$, the *composition* is the kernel from $X$ to $Z$
$$(\eta \circ \kappa)(x)(C) = \int_Y \eta(y)(C)\, \kappa(x)(dy).$$
For a measure $\mu$ on $X$, the measure $\kappa \circ \mu$ on $Y$ is $(\kappa \circ \mu)(B) = \int \kappa(x)(B)\, \mu(dx)$. It is the law of the second state of a process with the initial law $\mu$.

::: mathlib
`ProbabilityTheory.Kernel.comp` · `Mathlib.Probability.Kernel.Composition.Comp`

`η.comp κ`, with the notation `η ∘ₖ κ`, is the composition, and `Kernel.comp_apply` says that `(η ∘ₖ κ) a = (κ a).bind η`. `Kernel.lintegral_comp` is the iterated integral. `Kernel.comp_assoc`, `Kernel.comp_id` and `Kernel.id_comp` are the category laws. For a measure, the composition is `μ.bind κ`, with the notation `κ ∘ₘ μ`; the function `Measure.bind` is in the measure theory part of the library.

<?decl ProbabilityTheory.Kernel.comp?>
:::

**Definition (Composition-product).** For a kernel $\kappa$ from $X$ to $Y$ and a kernel $\eta$ from $X \times Y$ to $Z$, the *composition-product* is the kernel from $X$ to $Y \times Z$
$$(\kappa \otimes \eta)(x)(S) = \int_Y \int_Z \mathbf{1}_S(y, z)\, \eta(x, y)(dz)\, \kappa(x)(dy).$$
For a measure $\mu$ on $X$ and a kernel $\kappa$ from $X$ to $Y$, the measure $\mu \otimes \kappa$ on $X \times Y$ is $(\mu \otimes \kappa)(S) = \int_X \kappa(x)(S_x)\, \mu(dx)$, with $S_x = \{y : (x, y) \in S\}$. It is the joint law of $(X_0, X_1)$ when $X_0 \sim \mu$ and the law of $X_1$ given $X_0 = x$ is $\kappa(x)$.

::: mathlib
`ProbabilityTheory.Kernel.compProd` · `Mathlib.Probability.Kernel.Composition.CompProd`

`κ.compProd η`, with the notation `κ ⊗ₖ η`, is the composition-product. It is defined for s-finite kernels, and is `0` otherwise. `Kernel.compProd_apply` is the formula above, and `Kernel.lintegral_compProd` is the form for integrals. The measurability of the inner integral in `x` is the hard step of the construction, and it is a monotone class argument.

<?decl ProbabilityTheory.Kernel.compProd?>
:::

::: mathlib
`MeasureTheory.Measure.compProd` · `Mathlib.Probability.Kernel.Composition.MeasureCompProd`

`μ.compProd κ`, with the notation `μ ⊗ₘ κ`, is the measure on `α × β`, defined through `Kernel.compProd` with constant kernels. `Measure.compProd_apply` is the formula for a measurable set. For a constant kernel, `μ ⊗ₘ Kernel.const α ν` is the product measure `μ.prod ν`.

<?decl MeasureTheory.Measure.compProd?>
:::

The other operations are the following. `Kernel.prod κ η` is $x \mapsto \kappa(x) \otimes \eta(x)$, the product of two kernels with the same source (`Kernel.prod_apply`). `Kernel.map κ f` is $x \mapsto f_*\kappa(x)$ (`Kernel.map_apply`), and `Kernel.comap κ g hg` is $\kappa \circ g$. `Kernel.fst` and `Kernel.snd` are the marginals of a kernel to a product, and `Kernel.prodMkLeft` adds an unused variable to the source. The deterministic kernels connect the two kinds of operation: `Kernel.deterministic_comp_eq_map` and `Kernel.comp_deterministic_eq_comap`.

**Definition (Invariant measure).** A measure $\pi$ on $X$ is *invariant* for a kernel $\kappa$ from $X$ to $X$ if $\kappa \circ \pi = \pi$, that is, $\int \kappa(x)(B)\, \pi(dx) = \pi(B)$ for each measurable $B$.

::: mathlib
`ProbabilityTheory.Kernel.Invariant` · `Mathlib.Probability.Kernel.Invariance`

`κ.Invariant μ` is `μ.bind κ = μ` (`Kernel.Invariant.def`). `Kernel.Invariant.comp` says that a measure invariant for two kernels is invariant for their composition, so it is invariant for each power of one kernel.

<?decl ProbabilityTheory.Kernel.Invariant?>
:::

### Theorems and proofs

**Theorem (Associativity).** For kernels $\kappa : X \to Y$, $\eta : Y \to Z$ and $\xi : Z \to W$, $(\xi \circ \eta) \circ \kappa = \xi \circ (\eta \circ \kappa)$.

*Proof.* For a measurable $D \subseteq W$ and $x \in X$, both sides at $x$ give $D$ the value $\int_Y \int_Z \xi(z)(D)\, \eta(y)(dz)\, \kappa(x)(dy)$. For the left side this is the definition with $(\xi \circ \eta)(y)(D) = \int_Z \xi(z)(D)\, \eta(y)(dz)$. For the right side it is the integral of the measurable function $z \mapsto \xi(z)(D)$ against $(\eta \circ \kappa)(x)$, which is the iterated integral by `Kernel.lintegral_comp`. $\square$

**Theorem (Composition of Markov kernels).** If $\kappa$ and $\eta$ are Markov kernels, then $\eta \circ \kappa$ and $\kappa \otimes \eta$ are Markov kernels.

*Proof.* $(\eta \circ \kappa)(x)(Z) = \int \eta(y)(Z)\, \kappa(x)(dy) = \int 1\, \kappa(x)(dy) = 1$. For the composition-product, the inner integral of $\mathbf{1}_{Y \times Z}$ is $\eta(x, y)(Z) = 1$, and the outer integral is $\kappa(x)(Y) = 1$. $\square$

**Theorem (Markov chains and invariant laws).** Let $\kappa$ be a Markov kernel on $X$ and let $X_0, X_1, \ldots$ be a process with $X_0 \sim \mu$ and with the law of $X_{n+1}$ given $(X_0, \ldots, X_n)$ equal to $\kappa(X_n)$. Then $X_n \sim \kappa^n \circ \mu$. If $\mu$ is invariant, then each $X_n$ has the law $\mu$.

*Proof.* By induction, using that the law of $(X_n, X_{n+1})$ is $\mathcal{L}(X_n) \otimes \kappa$, and that its second marginal is $\kappa \circ \mathcal{L}(X_n)$. $\square$

Section 3 constructs such a process with the Ionescu-Tulcea theorem.

### Examples

**Example (The stationary law of a two-state chain).** Let $X = \{0, 1\}$ and let $\kappa(0) = (1 - p)\delta_0 + p\delta_1$ and $\kappa(1) = q\delta_0 + (1 - q)\delta_1$, with $0 < p, q < 1$. A measure $\pi = a\delta_0 + b\delta_1$ is invariant if $a(1 - p) + bq = a$, that is, $ap = bq$. With $a + b = 1$,
$$\pi = \frac{q}{p + q}\,\delta_0 + \frac{p}{p + q}\,\delta_1.$$
For $p = 0.1$ and $q = 0.3$, a machine that breaks with probability $0.1$ each day and is repaired with probability $0.3$ each day works $75\%$ of the days in the long run. The matrix $\begin{pmatrix} 1-p & p \\ q & 1-q \end{pmatrix}$ has the eigenvalues $1$ and $1 - p - q$, so $\kappa^n \circ \mu \to \pi$ at the rate $|1 - p - q|^n = 0.6^n$ for each initial law $\mu$.

**Example (A random sum as a composition).** Let $N$ have the Poisson law with mean $\lambda$, and given $N = n$ let $S$ be the number of heads in $n$ tosses of a coin with bias $r$. This is the kernel $\kappa(n) = \operatorname{Bin}(n, r)$ from $\mathbb{N}$ to $\mathbb{N}$, and the law of $S$ is $\kappa \circ \operatorname{Poi}(\lambda)$. A computation with generating functions shows that it is $\operatorname{Poi}(\lambda r)$: the thinning of a Poisson variable is a Poisson variable. The joint law of $(N, S)$ is $\operatorname{Poi}(\lambda) \otimes \kappa$.

**Counterexample (A family of probability measures that is not a kernel).** Let $A \subseteq [0, 1]$ be a set that is not Borel and let $\kappa(x) = \delta_1$ for $x \in A$ and $\kappa(x) = \delta_0$ otherwise. Each $\kappa(x)$ is a probability measure, but $x \mapsto \kappa(x)(\{1\}) = \mathbf{1}_A(x)$ is not measurable, so $\kappa$ is not a kernel. The integral $\int \kappa(x)(\{1\})\, \mu(dx)$ that defines a composition has no meaning.

### The library around it

The kernel files are in `Mathlib/Probability/Kernel/`. The directory `Composition` has the operations of this section, in separate files for `comp`, `compProd`, `prod`, `map` and `comap` and the relations between them, such as `Kernel.compProd_deterministic_apply`. `Mathlib/Probability/Kernel/Integral.lean` and `Composition/IntegralCompProd.lean` have the Bochner integrals against compositions, for example `Kernel.integral_comp`. `Mathlib/Probability/Kernel/MeasurableLIntegral.lean` proves the measurability of integrals against kernels, such as `Kernel.measurable_kernel_prodMk_left`.

The independence of Chapter 2 is a special case of `ProbabilityTheory.Kernel.Indep`, the independence with respect to a kernel and a measure. With the constant kernel it is the independence of Chapter 2, and with `condExpKernel` it is the conditional independence of Chapter 6.

The module `Mathlib.Probability.Kernel.Irreducible` defines the class `ProbabilityTheory.Kernel.IsIrreducible` $\varphi$ $\kappa$ for a kernel $\kappa$ from $\alpha$ to itself and a measure $\varphi$: for each measurable $A$ with $\varphi(A) > 0$ and each $a$, there is $n \ge 1$ with $\kappa^n(a)(A) > 0$. For a Markov chain, this means that each set of positive $\varphi$-measure can be reached from each state. The theorem `ProbabilityTheory.Kernel.isIrreducible_iff` unfolds the class, and `ProbabilityTheory.Kernel.isIrreducible_of_le_measure` says that irreducibility for $\varphi_2$ gives irreducibility for each $\varphi_1 \le \varphi_2$.

### Exercises

1. (A) Prove that $\kappa \circ \delta_x = \kappa(x)$ and that $\kappa \circ \operatorname{id} = \kappa$.
2. (A) Prove that $\operatorname{deterministic}(g) \circ \operatorname{deterministic}(f) = \operatorname{deterministic}(g \circ f)$.
3. (A) For the two-state chain, compute $\kappa^2(0)$ and verify that $\pi$ is invariant for $\kappa^2$.
4. (B) Prove that the second marginal of $\mu \otimes \kappa$ is $\kappa \circ \mu$, and that its first marginal is $\mu$ for a Markov kernel $\kappa$.
5. (B) Prove the thinning result of the second example with generating functions.
6. (B) Let $\kappa$ be a Markov kernel on a finite set with the matrix $P$. Prove that the invariant probability measures are the non-negative left eigenvectors of $P$ for the eigenvalue $1$ with sum $1$. Give a chain with two invariant laws.
7. (B) Prove that $\mu \otimes \operatorname{const}(\nu) = \mu \times \nu$ for finite measures $\mu$ and $\nu$.
8. (C) Prove that the simple random walk on $\mathbb{Z}$, the kernel $\kappa(x) = \frac{1}{2}(\delta_{x-1} + \delta_{x+1})$, has no invariant probability measure, and that the counting measure is invariant.

### Notes and history

Markov studied chains of dependent trials from 1906. The measure theoretic notion of a transition probability, with measurability in the starting point, is in Kolmogorov's work on Markov processes of 1931. The measurable structure on the space of probability measures that makes a kernel a measurable map is due to Giry, in 1982.

### Reference

<?reference?>
