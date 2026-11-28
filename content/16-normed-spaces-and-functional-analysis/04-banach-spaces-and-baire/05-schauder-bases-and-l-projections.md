---
title: Schauder bases and L-projections
kind: api
modules:
  - Mathlib.Analysis.Normed.Module.Bases
  - Mathlib.Analysis.Normed.Module.MStructure
explains:
  E2: [GeneralSchauderBasis, SchauderBasis, UnconditionalSchauderBasis, GeneralSchauderBasis.expansion, GeneralSchauderBasis.linearIndependent, SchauderBasis.exists_norm_proj_le, SchauderBasis.RankOneDecomposition, IsLprojection, IsMprojection, IsLprojection.Subtype.BooleanAlgebra]
  E1: auto
families: []
requires: [V07, V13, V14, V16.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Schauder bases and L-projections

### Overview

A Hamel basis of an infinite dimensional Banach space is uncountable, and its coordinates are not continuous. The useful notion of a basis in a Banach space is a Schauder basis: a sequence $(e_n)$ such that each vector is the sum of a unique convergent series $x = \sum_n a_n e_n$. The sequence spaces $\ell^p$ for $1 \le p < \infty$ and $c_0$ have the unit vectors as a Schauder basis. In a Banach space the partial sum projections $P_n x = \sum_{i < n} a_i e_i$ are uniformly bounded, and this is a consequence of the uniform boundedness principle of section 2.

The second module of the section treats a different kind of decomposition. An L-projection $P$ splits the norm as a sum, $\|x\| = \|P x\| + \|(1 - P) x\|$, and an M-projection splits the norm as a maximum. The band projections of an $L^1$ space are L-projections, and the L-projections of a space form a Boolean algebra. This structure theory gives a way to study the geometry of a general Banach space.

### The library around it

Mathlib gives one structure for all kinds of bases. The structure `GeneralSchauderBasis β 𝕜 X L` has a family of vectors `basis : β → X`, a family of coordinate functionals `coord : β → StrongDual 𝕜 X`, the biorthogonality relation `GeneralSchauderBasis.ortho`, and the expansion `GeneralSchauderBasis.expansion`. The expansion states that $x$ is the sum of $\sum_i \mathrm{coord}_i(x) \, e_i$ along a summation filter $L$. The summation filter chooses the meaning of the infinite sum. With `SummationFilter.conditional` on $\mathbb{N}$ the sum is the limit of the partial sums in the usual order. With `SummationFilter.unconditional` on a type `β` the sum is the limit over all finite subsets. The two abbreviations are `SchauderBasis 𝕜 X`, the classical case indexed by $\mathbb{N}$ with conditional sums, and `UnconditionalSchauderBasis β 𝕜 X`, the unconditional case on an arbitrary index type.

A basis coerces to a function `β → X`, so `b i` is the $i$-th basis vector. The coordinate functionals are continuous by definition, since they are elements of the dual. The lemma `GeneralSchauderBasis.linearIndependent` states that the basis vectors are linearly independent. A Schauder basis is not a `Module.Basis` in the sense of linear algebra, since a vector is in general an infinite combination of the basis vectors and not a finite one.

The projection onto a finite set $A$ of indices is `GeneralSchauderBasis.proj b A`, the map $x \mapsto \sum_{i \in A} \mathrm{coord}_i(x) \, e_i$. The lemma `GeneralSchauderBasis.proj_apply_basis_mem` computes it on a basis vector, `GeneralSchauderBasis.proj_comp` gives $P_A P_B = P_{A \cap B}$, and `GeneralSchauderBasis.range_proj_eq_span` identifies its range with the span of the basis vectors in $A$. The lemma `GeneralSchauderBasis.finrank_range_proj` states that this range has dimension $|A|$. The lemma `GeneralSchauderBasis.tendsto_proj` states that $P_A x$ tends to $x$ along the summation filter.

For a classical basis the projection `SchauderBasis.proj b n` is the partial sum projection onto the first $n$ vectors. The lemmas `SchauderBasis.proj_zero`, `SchauderBasis.proj_comp` and `SchauderBasis.tendsto_proj` give $P_0 = 0$, $P_n P_m = P_{\min(n, m)}$ and $P_n x \to x$. In a Banach space, `SchauderBasis.exists_norm_proj_le` states that there is a constant $C$ with $\|P_n\| \le C$ for all $n$. The proof applies the theorem of Banach-Steinhaus: for a fixed $x$ the sequence $P_n x$ converges, so it is bounded. The least such constant is the basis constant `SchauderBasis.nnNormProjBound`, with the bound `SchauderBasis.norm_proj_le_nnNormProjBound`. For an unconditional basis `UnconditionalSchauderBasis.exists_norm_proj_le` gives a uniform bound on the projections onto all finite sets, and `UnconditionalSchauderBasis.nnNormProjBound` is the unconditional constant.

The converse construction builds a basis from projections. A `SchauderBasis.RankOneDecomposition 𝕜 X` is a sequence of continuous projections $P_n$ with $P_0 = 0$, $P_n P_m = P_{\min(n,m)}$, $P_n x \to x$, a range of dimension $n$ for each $P_n$, and a nonzero vector $e_n$ in the range of each difference $P_{n+1} - P_n$. The map `SchauderBasis.RankOneDecomposition.basis` gives the Schauder basis with the vectors $e_n$, and `SchauderBasis.RankOneDecomposition.basis_proj` states that its partial sum projections are the $P_n$. The differences are `SchauderBasis.succSub P n`, and `SchauderBasis.sum_succSub` states that they sum to $P_n$. This construction is the usual way to show that a concrete space has a basis.

The module on M-structure works with an arbitrary ring $M$ that acts on a normed group $X$, so that it covers the bounded operators and other rings of multipliers. The predicate `IsLprojection X P` states that $P$ is idempotent and that $\|x\| = \|P x\| + \|(1 - P) x\|$ for all $x$. The predicate `IsMprojection X P` states the same with the maximum in place of the sum. The lemmas `IsLprojection.Lnorm` and `IsMprojection.Mnorm` extract the norm identities, and `IsLprojection.proj` and `IsMprojection.proj` extract the idempotence. The complement $1 - P$ of an L-projection is an L-projection, by `IsLprojection.Lcomplement`.

When the action is faithful, two L-projections commute, by `IsLprojection.commute`. Their product and the element $P + Q - P Q$ are L-projections, by `IsLprojection.mul` and `IsLprojection.join`. These facts give the instance `IsLprojection.Subtype.BooleanAlgebra` on the subtype of L-projections. The meet is the product and the join is $P + Q - P Q$, as `IsLprojection.coe_inf` and `IsLprojection.coe_sup` state, and the complement is $1 - P$ by `IsLprojection.coe_compl`. The order is given by `IsLprojection.le_def`: $P \le Q$ when $P$ is equal to $P \sqcap Q$, that is, when $P = P Q$. The library has no Boolean algebra of M-projections yet.

The two modules connect with the complemented subspaces of section 4. Each projection $P_n$ of a Schauder basis is a continuous projection with a finite dimensional range, so the span of the first $n$ basis vectors is complemented, and so is the closed span of the other vectors. Each L-projection and each M-projection is also a projection of norm at most $1$, so its range is a complemented subspace with a projection of norm at most $1$. In the space $\ell^1(A \cup B)$ for disjoint sets $A$ and $B$, the restriction to $A$ is an L-projection. In the space $\ell^\infty(A \cup B)$, the same restriction is an M-projection. These examples show the two kinds of summands in their simplest form.

#### Common errors

1. Treating a Schauder basis as a `Module.Basis`. A vector is an infinite sum of basis vectors, and the finite linear combinations are only dense. Use `GeneralSchauderBasis.expansion` and the coordinate functionals, and not the API of linear algebra.
2. Using the bound `SchauderBasis.exists_norm_proj_le` without completeness. The proof uses the theorem of Banach-Steinhaus and needs `[CompleteSpace X]`. A normed space that is not complete can have a basis with unbounded projections.
3. Expecting the Boolean algebra of L-projections without a faithful action. Most lemmas need `[FaithfulSMul M X]`. For operators on a space, the action of `X →L[𝕜] X` on the space is faithful.

### Exercises

1. (A) Describe the coordinate functionals and the partial sum projections of the unit vector basis of $\ell^2$, and show that the basis constant is $1$.
2. (A) Show that $P$ and $1 - P$ are both L-projections when one of them is, with `IsLprojection.Lcomplement_iff`.
3. (B) Prove `GeneralSchauderBasis.linearIndependent` from the biorthogonality relation `GeneralSchauderBasis.ortho`.
4. (B) On $\mathbb{R}^2$ with the norm $|x| + |y|$, show that the projection $(x, y) \mapsto (x, 0)$ is an L-projection. With the norm $\max(|x|, |y|)$, show that it is an M-projection.
5. (B) Show that the summing basis $f_n = e_0 + \dots + e_n$ of $c_0$ is a Schauder basis that is not unconditional.
6. (C) Prove `SchauderBasis.exists_norm_proj_le` from the uniform boundedness principle, and use it to show that each coordinate functional has norm at most $2C / \|e_n\|$.

### Reference

<?reference?>
