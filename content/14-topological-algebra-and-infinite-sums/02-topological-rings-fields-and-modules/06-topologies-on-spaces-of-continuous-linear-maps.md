---
title: Topologies on spaces of continuous linear maps
kind: api
modules:
  - Mathlib.Topology.Algebra.Module.Spaces.UniformConvergenceCLM
  - Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
  - Mathlib.Topology.Algebra.Module.Spaces.CompactConvergenceCLM
  - Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
  - Mathlib.Topology.Algebra.Module.UniformConvergence
explains:
  E2: [UniformConvergenceCLM, UniformConvergenceCLM.tendsto_iff_tendstoUniformlyOn, UniformConvergenceCLM.continuousSMul, UniformConvergenceCLM.completeSpace, ContinuousLinearMap.completeSpace, CompactConvergenceCLM, PointwiseConvergenceCLM, PointwiseConvergenceCLM.tendsto_iff_forall_tendsto, ContinuousLinearMap.postcomp, ContinuousLinearEquiv.arrowCongr]
  E1: auto
families: []
requires: [V07, V13.C01, V13.C04, V14.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Topologies on spaces of continuous linear maps

### Overview

The set of continuous linear maps from $E$ to $F$ is a vector space, and analysis needs a topology on it. There are several natural choices. A sequence of maps $f_n$ can converge to $f$ at each point, uniformly on compact sets, or uniformly on bounded sets. For normed spaces the last choice gives the operator norm topology. For general topological vector spaces there is no norm, but the three notions still make sense.

Mathlib uses one construction for all of them. For a family $\mathfrak{S}$ of subsets of $E$, the type `UniformConvergenceCLM σ F 𝔖` is a copy of `E →SL[σ] F` with the topology of uniform convergence on the sets of $\mathfrak{S}$. The bounded sets give the default topology on `E →SL[σ] F`, the compact sets give `CompactConvergenceCLM`, and the finite sets give `PointwiseConvergenceCLM`. This section describes the general construction and the three special cases.

### The library around it

#### The general construction

Let $E$ and $F$ be topological vector spaces, with $F$ a topological additive group, and let $\mathfrak{S}$ be a set of subsets of $E$. The type `UniformConvergenceCLM σ F 𝔖` has the notation `E →SLᵤ[σ, 𝔖] F`, and `E →Lᵤ[𝕜, 𝔖] F` for the case $\sigma = \mathrm{id}$. Its elements are continuous semilinear maps, and `ContinuousLinearMap.toUniformConvergenceCLM 𝔖` is the linear equivalence from `E →SL[σ] F`. The topology `UniformConvergenceCLM.instTopologicalSpace` is induced from the space `UniformOnFun` of all functions with the topology of uniform convergence on $\mathfrak{S}$. When $F$ is a uniform group, there is a uniform structure too, `UniformConvergenceCLM.instUniformSpace`, and the two structures agree (`UniformConvergenceCLM.uniformity_toTopologicalSpace_eq`).

Convergence is uniform convergence on each set of $\mathfrak{S}$:

$$f_i \to f \iff \forall S \in \mathfrak{S},\ f_i \to f \text{ uniformly on } S.$$

This is `UniformConvergenceCLM.tendsto_iff_tendstoUniformlyOn`. If $\mathfrak{S}$ is nonempty and directed by inclusion, the neighbourhoods of $0$ have the basis

$$\{\, f \mid f(S) \subseteq V \,\}, \qquad S \in \mathfrak{S},\ V \in \mathcal{N}_F(0),$$

by `UniformConvergenceCLM.hasBasis_nhds_zero`. The form `UniformConvergenceCLM.hasBasis_nhds_zero_of_basis` uses a basis of $\mathcal{N}_F(0)$ in place of all neighbourhoods.

| Lean name | Statement |
|---|---|
| `UniformConvergenceCLM.instIsTopologicalAddGroup` | the space is a topological additive group |
| `UniformConvergenceCLM.instIsUniformAddGroup` | with a uniform group $F$, it is a uniform additive group |
| `UniformConvergenceCLM.continuousSMul` | scalar multiplication is continuous if each $S \in \mathfrak{S}$ is bounded |
| `UniformConvergenceCLM.t2Space` | Hausdorff if $F$ is and $\bigcup \mathfrak{S} = E$ |
| `UniformConvergenceCLM.completeSpace` | complete if $F$ is, $\bigcup \mathfrak{S} = E$ and $E$ is coherent with $\mathfrak{S}$ |
| `UniformConvergenceCLM.topologicalSpace_mono` | a larger family $\mathfrak{S}$ gives a finer topology |
| `UniformConvergenceCLM.isVonNBounded_iff` | a set of maps is bounded if and only if its values on each $S \in \mathfrak{S}$ form a bounded set |
| `UniformConvergenceCLM.continuousEvalConst` | evaluation at a point is continuous if the point lies in some $S$ |

The condition in `UniformConvergenceCLM.continuousSMul` explains the choice of bounded sets. For $c \to 0$ in the field and a fixed map $f$, the map $c f$ tends to $0$ uniformly on $S$ only if $f(S)$ is bounded, and a continuous linear map sends bounded sets to bounded sets. The general statement behind it is in `Mathlib.Topology.Algebra.Module.UniformConvergence`: the lemma `UniformOnFun.continuousSMul_induced_of_image_bounded` gives continuity of scalar multiplication on a space of functions with the topology of uniform convergence on $\mathfrak{S}$, when the images of the sets of $\mathfrak{S}$ are bounded. The forms `UniformFun.continuousSMul_induced_of_range_bounded` and `UniformOnFun.continuousSMul_submodule_of_image_bounded` are for uniform convergence on the whole space and for a submodule.

The completeness condition `Topology.IsCoherentWith 𝔖` says that a set is open in $E$ when its trace on each $S \in \mathfrak{S}$ is open. A metrizable space is coherent with its compact sets and with its bounded sets.

Composition is continuous in each variable. `ContinuousLinearMap.precompUniformConvergenceCLM` composes on the right with a map $E' \to E$ that sends the sets of one family into sets of the other. `ContinuousLinearMap.postcompUniformConvergenceCLM` composes on the left with a map $F \to G$. The equivalence `ContinuousLinearEquiv.uniformConvergenceCLMCongr` changes the spaces by continuous linear equivalences.

#### The default topology: bounded convergence

The type `E →SL[σ] F` itself carries the topology of uniform convergence on von Neumann bounded sets, the instance `ContinuousLinearMap.topologicalSpace`. This is the topology of bounded convergence. For normed spaces it is the operator norm topology; Volume 16 treats that case. The default topology inherits the results of the general construction.

| Lean name | Statement |
|---|---|
| `ContinuousLinearMap.isTopologicalAddGroup` | a topological additive group |
| `ContinuousLinearMap.continuousSMul` | scalar multiplication is continuous |
| `ContinuousLinearMap.instT2Space` | Hausdorff if $F$ is |
| `ContinuousLinearMap.completeSpace` | complete if $F$ is and $E$ is coherent with its bounded sets |
| `ContinuousLinearMap.hasBasis_nhds_zero` | the basis $\{f \mid f(S) \subseteq V\}$ with $S$ bounded |
| `ContinuousLinearMap.isVonNBounded_iff` | a set of maps is bounded if and only if it is uniformly bounded on bounded sets |
| `ContinuousLinearMap.instContinuousEvalConst` | evaluation at a fixed point is continuous |

The maps between spaces of maps are these. `ContinuousLinearMap.precomp g` is $f \mapsto f \circ g$, and `ContinuousLinearMap.postcomp g` is $f \mapsto g \circ f$; both are continuous linear. `ContinuousLinearEquiv.arrowCongr e₁ e₂` is the equivalence $(E \to H) \simeq (F \to G)$ given by equivalences $E \simeq F$ and $H \simeq G$. For one space, `ContinuousLinearEquiv.conjContinuousAlgEquiv e` is the algebra equivalence $T \mapsto e \circ T \circ e^{-1}$ on endomorphisms. Other maps of this kind are `ContinuousLinearMap.prodL`, `ContinuousLinearMap.coprodEquivL`, `ContinuousLinearMap.smulRightL` and `ContinuousLinearMap.restrictScalarsL`. The embedding `ContinuousLinearMap.isUniformEmbedding_toUniformOnFun` relates the default topology to the space of functions.

The module also gives the map `ContinuousLinearMap.toLinearMap₁₂`, which turns a continuous bilinear map `E →L[𝕜] F →L[𝕜] G` into a bilinear map, with the injectivity lemma `ContinuousLinearMap.toLinearMap₁₂_injective`. The lemmas `ContinuousLinearMap.map_add₂` and `ContinuousLinearMap.map_smul₂` state linearity in the first variable.

#### Compact convergence

The type `CompactConvergenceCLM σ E F`, with the notation `E →SL_c[σ] F` and `E →L_c[𝕜] F`, takes $\mathfrak{S}$ to be the compact sets of $E$. The library gives the basis of neighbourhoods `CompactConvergenceCLM.hasBasis_nhds_zero`, the instances `CompactConvergenceCLM.instT2Space` and `CompactConvergenceCLM.continuousSMul`, the composition maps `ContinuousLinearMap.precompCompactConvergenceCLM` and `ContinuousLinearMap.postcompCompactConvergenceCLM`, and the equivalence `CompactConvergenceCLM.piEquivL` for maps into a product. A compact set is bounded, so this topology is coarser than the default one.

#### Pointwise convergence

The type `PointwiseConvergenceCLM σ E F`, with the notation `E →SLₚₜ[σ] F` and `E →Lₚₜ[𝕜] F`, takes $\mathfrak{S}$ to be the finite sets, so convergence is convergence at each point. This is `PointwiseConvergenceCLM.tendsto_iff_forall_tendsto`, and the topology is the strong operator topology. A map into the space is continuous if and only if each evaluation is continuous (`PointwiseConvergenceCLM.continuous_of_continuous_eval`). Evaluation at $x$ is the continuous linear map `PointwiseConvergenceCLM.evalCLM x`, and `PointwiseConvergenceCLM.isEmbedding_coeFn` embeds the space in the product $F^E$.

For $F$ the scalar field, the pointwise topology on the dual is the weak star topology. The equivalence `PointwiseConvergenceCLM.equivWeakDual` identifies `E →Lₚₜ[𝕜] 𝕜` with `WeakDual 𝕜 E`. The next section treats the weak dual in detail.

The three topologies are ordered: pointwise convergence is coarser than compact convergence, which is coarser than bounded convergence. All three follow from `UniformConvergenceCLM.topologicalSpace_mono`, because each finite set is compact and each compact set is bounded.

#### Common errors

1. A lemma about `E →SL[σ] F` does not apply to `E →SLₚₜ[σ] F`, although the elements are the same maps. Move between the types with `ContinuousLinearMap.toPointwiseConvergenceCLM` or `ContinuousLinearMap.toUniformConvergenceCLM`.
2. `UniformConvergenceCLM.hasBasis_nhds_zero` needs $\mathfrak{S}$ nonempty and directed. The family of all bounded sets is directed, but a family given by hand often is not; add finite unions first.
3. The default topology on `E →SL[σ] F` needs `IsTopologicalAddGroup F` as an instance. Without it, Lean finds no `TopologicalSpace` instance on the type of maps.

### Exercises

1. (A) Use `PointwiseConvergenceCLM.tendsto_iff_forall_tendsto` to prove that the maps $f_n(x) = x / n$ on $\mathbb{R}$ tend to $0$ pointwise.
2. (A) Show that $\{f \mid f(S) \subseteq V\}$ is a neighbourhood of $0$ for a bounded set $S$ and a neighbourhood $V$ of $0$ in $F$.
3. (B) On the space of sequences with finitely many nonzero terms and the supremum norm, give a sequence of continuous linear functionals that tends to $0$ pointwise but not uniformly on bounded sets.
4. (B) Explain why `UniformConvergenceCLM.continuousSMul` fails when $\mathfrak{S}$ contains an unbounded set, with $E = F = \mathbb{R}$ and $\mathfrak{S} = \{\mathbb{R}\}$.
5. (C) Prove that a set of continuous linear maps that is bounded for pointwise convergence and equicontinuous is bounded for compact convergence.

### Reference

<?reference?>
