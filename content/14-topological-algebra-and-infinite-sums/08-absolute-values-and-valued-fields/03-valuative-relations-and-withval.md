---
title: Valuative topologies and the type WithVal
kind: api
modules:
  - Mathlib.Topology.Algebra.ValuativeRel.Completion
  - Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
  - Mathlib.Topology.Algebra.Valued.LocallyCompact
  - Mathlib.Topology.Algebra.Valued.ValuativeRel
  - Mathlib.Topology.Algebra.Valued.WithVal
  - Mathlib.Topology.Algebra.Valued.WithZeroMulInt
explains:
  E2: [IsValuativeTopology, IsValuativeTopology.mem_nhds_iff, ValuativeRel.uniformSpace, Valuation.hasBasis_nhds_zero, Valuation.extension, UniformSpace.Completion.valuativeRel, WithVal, WithVal.equiv, Valuation.Completion, Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]
  E1: auto
families: []
requires: [V06, V13.C01, V13.C04, V14.C01, V14.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Valuative topologies and the type WithVal

### Overview

A valuation $v : R \to \Gamma_0$ gives a ring a topology, and the previous section describes it through the class `Valued`. Two valuations that order the elements of $R$ in the same way give the same topology. So the topology depends only on the relation $v(x) \le v(y)$, not on the values. The class `ValuativeRel R` of the algebra library records such a relation, and the class `IsValuativeTopology R` says that a topology on $R$ is the one that the relation defines. This form is the newer interface of the library, and it separates three pieces of data: the relation, the topology and a chosen valuation.

This section describes the valuative topology, the extension of the relation and of a valuation to the completion of a field, the type copy `WithVal v` that gives a ring the topology of one valuation, and the conditions for a valued field to be locally compact.

### The library around it

#### Valuative topologies

Let $R$ be a ring with `ValuativeRel R`. The relation $x \le_v y$ has a canonical valuation `ValuativeRel.valuation R` with values in the ordered monoid `ValuativeRel.ValueGroupWithZero R`. The class `IsValuativeTopology R` asks that a set $s$ is a neighbourhood of $x$ if and only if it contains a translate $x + \{z \mid v(z) < \gamma\}$ for a unit $\gamma$ of the value group. This is the field `IsValuativeTopology.mem_nhds_iff`.

| Lean name | Statement |
|---|---|
| `IsValuativeTopology.mem_nhds_zero_iff` | $s \in \mathcal{N}(0)$ if and only if $s$ contains a ball $\{z \mid v(z) < \gamma\}$ |
| `IsValuativeTopology.hasBasis_nhds_zero` | the balls form a basis at $0$ |
| `IsValuativeTopology.of_mem_nhds_zero_iff_vle` | a constructor that checks only the neighbourhoods of $0$ |
| `IsValuativeTopology.of_isInducing` | an inducing ring map gives a valuative topology on the source |
| `IsValuativeTopology.instIsTopologicalAddGroup` | the space is a topological additive group |
| `IsValuativeTopology.isTopologicalRing` | the space is a topological ring |
| `IsValuativeTopology.instT2Space` | a valued field with a valuative topology is Hausdorff |
| `IsValuativeTopology.continuous_valuation` | the valuation is continuous for the topology of the value group |

Most results are stated for a valuation $v$ that is compatible with the relation, written `[v.Compatible]`, so that a proof can choose a convenient valuation. The lemmas in the namespace `Valuation` have this form: `Valuation.hasBasis_nhds_zero`, `Valuation.mem_nhds_iff`, `Valuation.isClopen_ball`, `Valuation.isClopen_closedBall`, `Valuation.isClopen_sphere` and `Valuation.isClopen_integer`. As in each nonarchimedean ring, balls are open and closed, and `Valuation.locally_const` says that $v$ is constant near each point $x$ with $v(x) \ne 0$. The lemma `Valuation.cauchy_iff` describes the Cauchy filters by the balls, and `Valuation.discreteTopology_of_forall_lt` says that the topology is discrete when the nonzero values are bounded away from $0$.

The relation gives the topology and the uniform structure as definitions, not instances: `ValuativeRel.topologicalSpace` and `ValuativeRel.uniformSpace`. To give a ring the topology of a valuation $v$, first build the relation with `ValuativeRel.ofValuation v`, then use `ValuativeRel.uniformSpace`. The lemma `ValuativeRel.isValuativeTopology` says that the result satisfies the class.

The module `Mathlib.Topology.Algebra.Valued.ValuativeRel` connects the two interfaces. The instance `IsValuativeTopology.instValuedValueGroupWithZeroOfIsUniformAddGroup` gives a `Valued` structure to a uniform additive group with a valuative topology, and `IsValuativeTopology.v_eq_valuation` says that its valuation is the canonical one. The module also has the notations `𝒪[K]` for the valuation ring, `𝓂[K]` for its maximal ideal and `𝓀[K]` for the residue field.

#### Extension to the completion

Let $K$ be a field with a valuative topology and a uniform structure, and let $v$ be a compatible valuation. Then $v$ extends to the completion $\hat{K}$.

1. `Valuation.extension v` is the extended valuation on `UniformSpace.Completion K`, and `Valuation.extension_apply_coe` says that it agrees with $v$ on $K$.
2. `Valuation.hasBasis_nhds_coe_zero` says that the balls of the extension form a basis at $0$ in $\hat{K}$.
3. `UniformSpace.Completion.valuativeRel` is the relation on $\hat{K}$, and `UniformSpace.Completion.isValuativeTopology` says that the topology of the completion is its valuative topology.
4. `Valuation.compatible_extension` says that the extension of a compatible valuation is compatible with the relation on $\hat{K}$.
5. `Valuation.isEquiv_extension` says that two compatible valuations have equivalent extensions.
6. `Valuation.extension_surjective_iff` describes when the extension takes the same values as $v$.

The proof of the extension uses `Valuation.extension_locally_const`: the valuation is locally constant away from $0$, so it extends by continuity from the dense subfield $K$. The field structure of $K$ enters through the estimate `Valuation.inversion_estimate`, which controls $v(x^{-1} - y^{-1})$ for $x$ near $y$. The instance `IsValuativeTopology.instCompletableTopFieldOfIsUniformAddGroup` then makes the completion a field.

#### The type copy WithVal

A ring can carry several valuations, such as the $p$-adic valuations of $\mathbb{Q}$ for different primes $p$, and each gives a different topology. The type `WithVal v` is a copy of $R$ with the topology and the uniform structure of the valuation $v$. The equivalence `WithVal.equiv v : WithVal v ≃+* R` moves terms between the copy and $R$, and the maps `WithVal.toVal` and `WithVal.ofVal` are its two directions.

| Lean name | Statement |
|---|---|
| `WithVal.instValued` | the copy is a valued ring with valuation $v$ |
| `WithVal.valuation` | the valuation on the copy |
| `WithVal.instIsValuativeTopology` | the topology of the copy is the valuative topology |
| `WithVal.toVal_add` | the map $R \to$ `WithVal v` respects addition |
| `WithVal.congr` | equivalent valuations give equivalent copies |
| `WithVal.uniformEquiv` | equivalent valuations give uniformly equivalent copies |
| `Valuation.IsEquiv.uniformContinuous_equiv` | the identity between two copies is uniformly continuous |
| `Valuation.Completion` | the completion of the copy, the completion of $K$ for $v$ |

The copy keeps the algebra of $R$: it is a ring, a field when $R$ is a field, an algebra, a number field when $R$ is a number field, and a fraction field when $R$ is a fraction field. The completion `Valuation.Completion v` gives the $v$-adic completion of $K$. The completion of the fraction field of a Dedekind domain at a height one prime is built in this way.

#### Locally compact valued fields

Let $K$ be a field with a valuation of rank one, so that $K$ is a normed field. The module `Mathlib.Topology.Algebra.Valued.LocallyCompact` gives the conditions for $K$ to be locally compact, the setting of local fields.

| Lean name | Statement |
|---|---|
| `Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField` | $\mathcal{O}_K$ is compact if and only if it is complete, a discrete valuation ring, and has a finite residue field |
| `Valued.integer.properSpace_iff_compactSpace_integer` | $K$ is proper if and only if $\mathcal{O}_K$ is compact |
| `Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField` | the same conditions for $K$ |
| `Valued.integer.totallyBounded_iff_finite_residueField` | for a discrete valuation ring, $\mathcal{O}_K$ is totally bounded if and only if the residue field is finite |
| `Valued.integer.isDiscreteValuationRing_of_compactSpace` | a compact valuation ring of a nontrivial valuation is a discrete valuation ring |
| `Irreducible.maximalIdeal_eq_closedBall` | the maximal ideal is the closed ball of radius $\lVert \varpi \rVert$ for a uniformizer $\varpi$ |

The proof of the first result uses `Irreducible.maximalIdeal_pow_eq_closedBall_pow`. The ideal $\mathfrak{m}^n$ is a closed ball, and the cosets of $\mathfrak{m}^n$ in $\mathcal{O}_K$ correspond to the elements of $\mathcal{O}_K / \mathfrak{m}^n$, a finite set when the residue field is finite. So for each $n$ the ring $\mathcal{O}_K$ is covered by finitely many balls of radius $\lVert \varpi \rVert^n$, and it is totally bounded. With completeness, it is compact. The field $\mathbb{Q}_p$ satisfies the three conditions.

The module `Mathlib.Topology.Algebra.Valued.WithZeroMulInt` treats valuations with values in $\mathbb{Z}_{m0}$, the multiplicative integers with a zero. The lemma `Valued.tendsto_zero_pow_of_v_lt_one` says that $x^n \to 0$ when $v(x) < 1$ and the value group is archimedean, and `Valued.tendsto_zero_pow_of_le_exp_neg_one` is the form for $\mathbb{Z}_{m0}$.

#### Common errors

1. `ValuativeRel.uniformSpace` is a definition, not an instance. A ring with `ValuativeRel R` has no topology until a proof or a definition installs one.
2. A lemma about `Valued` does not apply to `IsValuativeTopology` at once. The bridge instance in `Mathlib.Topology.Algebra.Valued.ValuativeRel` needs `IsUniformAddGroup R`.
3. `WithVal v` is a structure, so a term of $R$ is not a term of `WithVal v`. Use `WithVal.toVal` and `WithVal.ofVal`, or `WithVal.equiv v`, to move between them. The two types have different topologies, so a proof must not mix them.

### Exercises

1. (A) Prove that a ball $\{x \mid v(x) < \gamma\}$ is closed with `Valuation.isClopen_ball`.
2. (A) Use `Valued.tendsto_zero_pow_of_v_lt_one` to prove that $p^n \to 0$ in $\mathbb{Q}_p$.
3. (B) Show that the valuation ring of a field with a valuative topology is open and closed.
4. (B) Prove that $\mathbb{F}_p((t))$, the field of Laurent series, has a compact valuation ring, and check each condition of the main result of `Mathlib.Topology.Algebra.Valued.LocallyCompact`.
5. (C) Explain why the field $\mathbb{C}((t))$ with the $t$-adic valuation is complete but not locally compact.

### Reference

<?reference?>
