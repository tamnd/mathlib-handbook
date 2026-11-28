---
title: Uniform convergence and equicontinuity
kind: api
modules:
  - Mathlib.Topology.UniformSpace.UniformConvergence
  - Mathlib.Topology.UniformSpace.LocallyUniformConvergence
  - Mathlib.Topology.UniformSpace.UniformApproximation
  - Mathlib.Topology.UniformSpace.Dini
  - Mathlib.Topology.UniformSpace.ProdApproximation
  - Mathlib.Topology.UniformSpace.UniformConvergenceTopology
  - Mathlib.Topology.UniformSpace.CompactConvergence
  - Mathlib.Topology.UniformSpace.Equicontinuity
  - Mathlib.Topology.UniformSpace.Ascoli
  - Mathlib.Topology.UniformSpace.Path
explains:
  E2: [TendstoUniformly, TendstoUniformlyOnFilter, UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto, TendstoUniformly.continuous, tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace, UniformFun.tendsto_iff_tendstoUniformly, UniformOnFun.tendsto_iff_tendstoUniformlyOn, EquicontinuousAt, Filter.Tendsto.continuous_of_equicontinuous, ArzelaAscoli.isCompact_of_equicontinuous]
  E1: auto
families: []
requires: [V13.C02, V13.C05, V13.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Uniform convergence and equicontinuity

### Overview

A sequence of functions $F_n : X \to Y$ converges uniformly to $f$ if, for each entourage $V$ of $Y$, the pair $(f(x), F_n(x))$ is in $V$ for all $x$ and all large $n$. For a metric space $Y$ this is the condition $\sup_x d(f(x), F_n(x)) \to 0$. Uniform convergence keeps continuity, and so it is the basic tool of analysis on function spaces. This section describes the predicates for uniform convergence and its local forms, the uniform structures on function spaces that make these predicates into convergence in a topology, the theorem of Dini, and equicontinuity with the theorem of Arzelà and Ascoli.

The predicates need only a uniform structure on the target $Y$. The local forms need a topology on the source $X$. The section uses filters from Chapter 2 and compactness from Chapter 5. Chapter 11 applies these results to the space `C(X, Y)` of bundled continuous maps.

### The library around it

#### The predicates of uniform convergence

The module `Mathlib.Topology.UniformSpace.UniformConvergence` defines a family of predicates. Each one takes a family `F : ι → α → β`, a limit `f : α → β` and a filter $p$ on the index type. The filter is `Filter.atTop` for a sequence.

| Lean name | Meaning |
|---|---|
| `TendstoUniformly F f p` | for each entourage $V$, eventually in $p$, $(f(x), F_i(x)) \in V$ for all $x$ |
| `TendstoUniformlyOn F f p s` | the same for all $x \in s$ |
| `TendstoUniformlyOnFilter F f p p'` | the same, eventually for $(i, x)$ in $p \times p'$ |
| `UniformCauchySeqOn F p s` | for each $V$, eventually in $p \times p$, $(F_i(x), F_j(x)) \in V$ for $x \in s$ |

The most general form is `TendstoUniformlyOnFilter`. The two others are its special cases for the principal filter of $s$ and for the filter $\top$, by `tendstoUniformlyOn_iff_tendstoUniformlyOnFilter` and `tendstoUniformly_iff_tendstoUniformlyOnFilter`. Each predicate has lemmas with the same suffixes, for example `TendstoUniformlyOn.mono`, `TendstoUniformlyOn.congr`, `TendstoUniformly.comp`, `TendstoUniformly.prodMk` and `TendstoUniformly.prodMap`. The suffix tendsto_at gives pointwise convergence, as in `TendstoUniformly.tendsto_at`. A uniformly continuous map $g$ keeps uniform convergence, `UniformContinuous.comp_tendstoUniformly`.

A uniformly Cauchy family that converges pointwise converges uniformly, `UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto`. The proof: take an entourage $V$ and a closed symmetric $W$ with $W \circ W \subseteq V$. Eventually $(F_i(x), F_j(x)) \in W$ for all $x \in s$. Let $j \to \infty$: since $W$ is closed, $(F_i(x), f(x)) \in W$. In a complete space, each uniformly Cauchy family converges pointwise, so it converges uniformly.

#### Local uniform convergence

The module `Mathlib.Topology.UniformSpace.LocallyUniformConvergence` defines `TendstoLocallyUniformly F f p`: each point $x$ has a neighbourhood $t$ on which $F$ converges uniformly to $f$. The relative form is `TendstoLocallyUniformlyOn F f p s`. Uniform convergence implies local uniform convergence, `TendstoUniformly.tendstoLocallyUniformly`. On a compact space the two agree, `tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace`. The proof of the hard direction uses a finite subcover: cover $X$ by the neighbourhoods $t_x$, take finitely many, and take the latest index of the finitely many conditions. In a locally compact space, local uniform convergence is uniform convergence on each compact set, `tendstoLocallyUniformly_iff_forall_isCompact`. The theorem `tendstoLocallyUniformlyOn_tfae` lists the equivalent forms on an open set.

#### Continuity of the limit

The module `Mathlib.Topology.UniformSpace.UniformApproximation` proves that a uniform limit of continuous functions is continuous: `TendstoUniformly.continuous`, `TendstoUniformlyOn.continuousOn` and `TendstoLocallyUniformly.continuous`. The hypothesis is weak: it is enough that $F_i$ is continuous for frequently many $i$. The base result is `continuous_of_uniform_approx_of_continuous`. If for each entourage $V$ there is a continuous $F$ with $(f(y), F(y)) \in V$ for all $y$, then $f$ is continuous. The proof is the $\varepsilon/3$ argument with entourages: for $V$, take a symmetric $W$ with $W \circ W \circ W \subseteq V$, and a continuous $F$ that is $W$-close to $f$. Near $x$, $F(y)$ is $W$-close to $F(x)$, so $f(y)$ is $V$-close to $f(x)$. The same module proves that a uniform limit of uniformly continuous functions is uniformly continuous, `TendstoUniformly.uniformContinuous`.

#### Dini's theorem

The module `Mathlib.Topology.UniformSpace.Dini` proves Dini's theorem. Let $X$ be compact, and let $F_n$ be a monotone family of continuous functions to an ordered normed group $G$, for example $\mathbb{R}$. If $F_n$ converges pointwise to a continuous $f$, then it converges uniformly. This is `Monotone.tendstoUniformly_of_forall_tendsto`, with the dual `Antitone.tendstoUniformly_of_forall_tendsto` and the local forms `Monotone.tendstoLocallyUniformly_of_forall_tendsto`. For bundled maps the result is `ContinuousMap.tendsto_of_monotone_of_pointwise`. Here $G$ has a solid norm, `HasSolidNorm G`, so that $|a| \le |b|$ implies $\|a\| \le \|b\|$.

#### Spaces with the uniformity of uniform convergence

The predicates become convergence in a space through two type synonyms in `Mathlib.Topology.UniformSpace.UniformConvergenceTopology`. The type `UniformFun α β`, with the notation `α →ᵤ β`, is the type of functions with the uniformity of uniform convergence. Its entourages have the basis `UniformFun.gen α β V`, the set of pairs $(f, g)$ with $(f(x), g(x)) \in V$ for all $x$. The type `UniformOnFun α β 𝔖`, with the notation `α →ᵤ[𝔖] β`, has the uniformity of uniform convergence on each member of a family $\mathfrak{S}$ of subsets. The maps `UniformFun.ofFun` and `UniformFun.toFun` move between the synonym and the function type.

The key lemmas say that convergence in these spaces is uniform convergence: `UniformFun.tendsto_iff_tendstoUniformly` and `UniformOnFun.tendsto_iff_tendstoUniformlyOn`. Both spaces are complete when $\beta$ is complete, `UniformFun.instCompleteSpace` and `UniformOnFun.instCompleteSpace`. The continuous functions form a closed set, `UniformFun.isClosed_setOfPred_continuous`, which restates the continuity of a uniform limit. The constructions follow the lattice of uniformities: `UniformFun.comap_eq`, `UniformFun.inf_eq`, `UniformOnFun.iInf_eq`, and the uniform equivalences `UniformFun.uniformEquivProdArrow` and `UniformFun.uniformEquivPiComm`.

The module `Mathlib.Topology.UniformSpace.CompactConvergence` puts on `C(α, β)` the uniformity of uniform convergence on compact sets, `ContinuousMap.compactConvergenceUniformSpace`. It induces the compact-open topology of Chapter 11. The map to `UniformOnFun` for the compact sets is a uniform embedding, `ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact`. Convergence in `C(α, β)` is uniform convergence on each compact set, `ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn`. If $\alpha$ is weakly locally compact, it is local uniform convergence, `ContinuousMap.tendsto_iff_tendstoLocallyUniformly`, and if $\alpha$ is compact, it is uniform convergence, `ContinuousMap.tendsto_iff_tendstoUniformly`. Completeness holds for a compactly coherent source, `ContinuousMap.instCompleteSpaceOfCompactlyCoherentSpace`.

The module `Mathlib.Topology.UniformSpace.Path` gives the space of paths `Path x y` the uniformity of uniform convergence, `Path.instUniformSpace`, with `Path.instCompleteSpace` and the uniform continuity of the operations, `Path.uniformContinuous_trans` and `Path.uniformContinuous_symm`. The module `Mathlib.Topology.UniformSpace.ProdApproximation` approximates a continuous function $f$ on $X \times Y$, for a compact totally disconnected space $X$, by finite sums of products $g(x) h(y)$, `ContinuousMap.exists_finite_sum_mul_approximation_of_mem_uniformity`.

#### Equicontinuity

The module `Mathlib.Topology.UniformSpace.Equicontinuity` defines `EquicontinuousAt F x₀` for a family `F : ι → X → α`: for each entourage $V$, there is a neighbourhood of $x_0$ on which $(F_i(x_0), F_i(x)) \in V$ for all $i$ at the same time. The family is `Equicontinuous F` if it is equicontinuous at each point. The uniform form is `UniformEquicontinuous F`, which implies `Equicontinuous F` by `UniformEquicontinuous.equicontinuous`. Each predicate has a form for sets of functions, such as `Set.Equicontinuous`, and the relative forms `EquicontinuousOn` and `EquicontinuousWithinAt`.

Equicontinuity makes pointwise convergence as good as uniform convergence for continuity. If an equicontinuous family converges pointwise to $f$, then $f$ is continuous, `Filter.Tendsto.continuous_of_equicontinuous`. The proof is short. For $V$, take a closed $W$ with $W \circ W \subseteq V$, and a neighbourhood $t$ of $x_0$ on which each $F_i$ is $W$-close to $F_i(x_0)$. Pass to the limit in $i$: since $W$ is closed, $f(x)$ is $W$-close to $f(x_0)$ on $t$. By the same argument, the closure of an equicontinuous set of functions in the product topology is equicontinuous, `Set.Equicontinuous.closure`.

#### The theorem of Arzelà and Ascoli

The module `Mathlib.Topology.UniformSpace.Ascoli` proves the theorem of Arzelà and Ascoli in general form. On an equicontinuous family, the topology of pointwise convergence and the topology of uniform convergence on compact sets agree, `EquicontinuousOn.isUniformInducing_uniformOnFun_iff_pi`, and on a compact space the uniform structures agree, `Equicontinuous.isUniformInducing_uniformFun_iff_pi`. With the theorem of Tychonoff this gives compactness. The form for bundled maps is `ArzelaAscoli.isCompact_of_equicontinuous`: a set $S$ of continuous maps $X \to \alpha$ is compact in `C(X, α)` if it is equicontinuous and its image in the product $\alpha^X$ is compact. The theorems `ArzelaAscoli.compactSpace_of_isClosedEmbedding` and `ArzelaAscoli.isCompact_closure_of_isClosedEmbedding` give the forms for a family in `UniformOnFun`.

#### Common errors

1. In `TendstoUniformly F f p` the pair in the entourage is $(f(x), F_i(x))$, with the limit first. A lemma about entourages that are not symmetric can need the pair in this order.
2. The type `α →ᵤ β` is a type synonym. A function `f : α → β` must go through `UniformFun.ofFun` to become a point of it, or the instance of the product topology on `α → β` is used.
3. `TendstoUniformly.continuous` asks for continuity of $F_i$ for frequently many indices, as `∃ᶠ i in p, Continuous (F i)`. For a sequence and `Filter.atTop`, use `Filter.Eventually.frequently` to get this from an eventual statement.

### Exercises

1. (A) Show that $F_n(x) = x^n$ converges pointwise on $[0, 1]$ but not uniformly. Use `TendstoUniformlyOn.continuousOn`.
2. (A) Prove `UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto`.
3. (B) Prove that local uniform convergence on a compact space is uniform convergence.
4. (B) Prove Dini's theorem for real functions on a compact space.
5. (B) Prove that the pointwise limit of an equicontinuous family of functions is continuous.
6. (C) Prove the theorem of Arzelà and Ascoli for a compact metric space $X$: a set of functions in `C(X, ℝ)` is relatively compact if it is equicontinuous and pointwise bounded.

### Reference

<?reference?>
