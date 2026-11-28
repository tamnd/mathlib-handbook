---
title: Polish spaces, the Baire space and the Cantor space
kind: api
modules:
  - Mathlib.Topology.MetricSpace.PiNat
  - Mathlib.Topology.MetricSpace.Polish
  - Mathlib.Topology.MetricSpace.CantorScheme
  - Mathlib.Topology.MetricSpace.Perfect
  - Mathlib.Topology.MetricSpace.HausdorffAlexandroff
explains:
  E2: [PiNat.dist_triangle_nonarch, PiNat.mem_cylinder_iff_dist_le, PiNat.exists_lipschitz_retraction_of_isClosed, exists_nat_nat_continuous_surjective_of_completeSpace, IsGδ.polishSpace, PolishSpace.IsClopenable.iUnion, CantorScheme.VanishingDiam.map_continuous, Perfect.exists_nat_bool_injection, exists_nat_bool_continuous_surjective_of_compact]
  E1: auto
families: []
requires: [V13.C01, V13.C02, V13.C03, V13.C05, V13.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Polish spaces, the Baire space and the Cantor space

### Overview

A Polish space is a separable topological space whose topology comes from a complete metric. The class contains $\mathbb{R}^n$, separable Banach spaces, compact metric spaces and their closed and open subsets. It is the natural setting of descriptive set theory and of much of probability theory. Two spaces of sequences play a central part in the theory: the Baire space $\mathbb{N}^{\mathbb{N}}$, written `ℕ → ℕ`, and the Cantor space $2^{\mathbb{N}}$, written `ℕ → Bool`. Each nonempty Polish space is a continuous image of the Baire space, and each nonempty compact metric space is a continuous image of the Cantor space.

This section uses the complete metric spaces and the Baire theorem of Chapter 3 and the compact metric spaces of Chapter 5. It first describes the metric on spaces of sequences, then the class `PolishSpace` and its closure properties. The last part describes schemes, the tool that builds maps from the Cantor space, and two theorems that use them: the Cantor space embeds in each nonempty perfect set of a complete space, and it maps onto each nonempty compact metric space.

### The library around it

#### The metric on a space of sequences

Let $E_0, E_1, \dots$ be types and consider the product $\prod_n E_n$, written `∀ n, E n`. For two sequences $x \ne y$, `PiNat.firstDiff x y` is the first index $n$ with $x_n \ne y_n$. The distance `PiNat.dist` is
$$d(x, y) = (1/2)^{\mathrm{firstDiff}(x, y)}$$
for $x \ne y$, and $d(x, x) = 0$ (`PiNat.dist_eq_of_ne`). So two sequences are close when they agree on a long initial part. The basic sets are the cylinders: `PiNat.cylinder x n` is the set of sequences that agree with $x$ at the indices $i < n$ (`PiNat.mem_cylinder_iff`). The function `PiNat.res x n` is the list of the first $n$ terms, in reverse order, and `PiNat.cylinder_eq_res` describes the cylinder with it.

**Proposition** (`PiNat.dist_triangle_nonarch`). The distance is an ultrametric: $d(x, z) \le \max(d(x, y), d(y, z))$.

*Proof.* Suppose that $x$ agrees with $y$ below $m$ and $y$ agrees with $z$ below $k$. Then $x$ agrees with $z$ below $\min(m, k)$, so $\mathrm{firstDiff}(x, z) \ge \min(\mathrm{firstDiff}(x, y), \mathrm{firstDiff}(y, z))$ (`PiNat.min_firstDiff_le`). The map $n \mapsto (1/2)^n$ is decreasing.

**Proposition** (`PiNat.mem_cylinder_iff_dist_le`). $y \in \mathrm{cylinder}(x, n)$ if and only if $d(y, x) \le (1/2)^n$.

*Proof.* Both sides say that $\mathrm{firstDiff}(y, x) \ge n$, or $y = x$.

So the cylinders are the closed balls, and in an ultrametric space each ball is open and closed. When each $E_n$ has the discrete topology, the cylinders are open (`PiNat.isOpen_cylinder`) and form a basis of the product topology (`PiNat.isTopologicalBasis_cylinders`). Then `PiNat.metricSpace` is a metric space structure whose topology is the product topology, and the space is complete (`PiNat.completeSpace`). The structure is a definition and not a global instance, because the product type already has a topology and a uniform structure from the library, and a global metric instance would give a second uniform structure that is not definitionally the same. A proof activates it with `attribute [local instance] PiNat.metricSpace`. The definitions `PiNat.metricSpaceOfDiscreteUniformity` and `PiNat.metricSpaceNatNat` give the variants that also match a given uniform structure.

For a countable product of arbitrary metric spaces, `PiCountable.dist` uses an encoding of the index: $d(x, y) = \sum_i \min(2^{-\mathrm{encode}(i)}, d(x_i, y_i))$ (`PiCountable.dist_eq_tsum`). The structure `PiCountable.metricSpace` is again a local instance, and `PiCountable.dist_le_dist_pi_of_dist_lt` compares one coordinate with the whole distance. With it, `Metric.PiNatEmbed.exists_embedding_to_hilbert_cube` embeds each separable metric space in the Hilbert cube $[0, 1]^{\mathbb{N}}$, through the map $x \mapsto (\min(d(x, x_n), 1))_n$ for a dense sequence $(x_n)$. The lemma `Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating` uses the same idea: a compact space with a sequence of continuous maps to metric spaces that separates points is metrizable.

#### Retractions onto closed sets

In an ultrametric space of sequences, a closed set is a retract of the whole space, and the retraction can be $1$-Lipschitz.

**Theorem** (`PiNat.exists_lipschitz_retraction_of_isClosed`). Let each $E_n$ be discrete, and let $s$ be a nonempty closed set of sequences. There is a map $f$ with $f(x) = x$ for $x \in s$, range $s$, and Lipschitz constant $1$.

*Proof sketch.* For $x \notin s$, let $n$ be the length of the longest initial part of $x$ that is also the initial part of a point of $s$ (`PiNat.longestPrefix`). It is finite because $s$ is closed (`PiNat.exists_disjoint_cylinder`). Choose a point $f(x)$ of $s$ in the cylinder of $x$ of length $n$, with one choice for each such cylinder. A short case analysis on the first differences shows $d(f(x), f(y)) \le d(x, y)$.

The theorem gives the universal property of the Baire space.

**Theorem** (`exists_nat_nat_continuous_surjective_of_completeSpace`). Each nonempty complete metric space $\alpha$ with a countable basis is the image of a continuous map `(ℕ → ℕ) → α`.

*Proof sketch.* Fix a dense sequence $(a_k)$ in $\alpha$. Let $s$ be the set of sequences $(k_n)$ in $\mathbb{N}^{\mathbb{N}}$ with $d(a_{k_n}, a_{k_{n+1}}) < (1/2)^n$. The set $s$ is closed, and for $k \in s$ the sequence $(a_{k_n})$ is Cauchy, so it has a limit $g(k)$. The map $g$ is continuous on $s$, and it is onto by density. Compose it with a retraction of $\mathbb{N}^{\mathbb{N}}$ onto $s$.

#### Polish spaces

The class `PolishSpace α` extends `SecondCountableTopology α` and `TopologicalSpace.IsCompletelyMetrizableSpace α`. It does not fix a metric. A proof that needs a complete metric chooses one with `let := TopologicalSpace.upgradeIsCompletelyMetrizable α`. The instance `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace` gives a Polish space from separability and complete metrizability. A complete separable metric space is Polish, and `PolishSpace.instENNReal` makes $[0, \infty]$ Polish. The theorem `PolishSpace.exists_nat_nat_continuous_surjective` restates the universal property of the Baire space for Polish spaces.

| Lean name | Statement |
|---|---|
| `IsClosed.polishSpace` | a closed subset of a Polish space is Polish |
| `IsOpen.polishSpace` | an open subset of a Polish space is Polish |
| `IsGδ.polishSpace` | a $G_\delta$ subset of a Polish space is Polish |
| `Topology.IsClosedEmbedding.polishSpace` | the source of a closed embedding into a Polish space is Polish |
| `Equiv.polishSpace_induced` | a type in bijection with a Polish space, with the induced topology, is Polish |
| `IsGδ.isCompletelyMetrizableSpace` | a $G_\delta$ subset of a completely metrizable space is completely metrizable |

The restriction of a complete metric to an open set is not complete in general, so the open case already needs a new metric. For an open set $U$, the metric $d'(x, y) = d(x, y) + |1/d(x, U^c) - 1/d(y, U^c)|$ gives the same topology on $U$ and is complete, because a Cauchy sequence for $d'$ stays away from the boundary. The library does not use this metric directly. It treats all $G_\delta$ sets at once with the same idea.

**Theorem** (`IsGδ.polishSpace`). A $G_\delta$ subset of a Polish space is Polish.

*Proof sketch.* Write $s = \bigcap_i U_i$ with each $U_i$ open. The map `GδEmbedding.gδEmbedding U` sends $x \in s$ to $(x, (1/d(x, U_i^c))_i)$, a point of $\alpha \times [0, \infty)^\iota$. It is a closed embedding (`GδEmbedding.isClosedEmbedding_gδEmbedding`), and the target is Polish, so `Topology.IsClosedEmbedding.polishSpace` applies.

#### Clopenable sets

Some proofs about Borel sets change the topology. The predicate `PolishSpace.IsClopenable s` says that there is a finer Polish topology in which $s$ is open and closed. The key lemma is `PolishSpace.exists_polishSpace_forall_le`: for countably many Polish topologies $t_n$ finer than the given one, there is one Polish topology finer than all of them. It is a consequence of `PolishSpace.iInf`, which gives a Polish topology as a countable infimum, built from the diagonal embedding into the product.

| Lean name | Statement |
|---|---|
| `IsClosed.isClopenable` | each closed set is clopenable |
| `IsOpen.isClopenable` | each open set is clopenable |
| `PolishSpace.IsClopenable.compl` | the complement of a clopenable set is clopenable |
| `PolishSpace.IsClopenable.iUnion` | a countable union of clopenable sets is clopenable |

**Theorem** (`PolishSpace.IsClopenable.iUnion`). If each $s_n$ is clopenable, so is $\bigcup_n s_n$.

*Proof sketch.* Take a Polish topology $t_n$ for each $n$ in which $s_n$ is open and closed. By `PolishSpace.exists_polishSpace_forall_le`, there is one Polish topology $t'$ finer than all $t_n$. In $t'$ each $s_n$ is open, so the union is open. An open set is clopenable by `IsOpen.isClopenable`, applied to $t'$, and a topology finer than $t'$ is finer than the original one.

So the clopenable sets form a $\sigma$-algebra that contains the open sets. In measure theory, this gives that each Borel set of a Polish space is clopenable. That step and its converse use measurable sets, and they are outside this volume.

#### Schemes

A scheme on $\alpha$ indexed by $\beta$ is a map $A$ from the finite lists of elements of $\beta$ to the subsets of $\alpha$. A sequence $x : \mathbb{N} \to \beta$ is a branch, and along a branch the sets are $A(\mathrm{res}(x, n))$. The partial map `CantorScheme.inducedMap A` sends $x$ to a point of $\bigcap_n A(\mathrm{res}(x, n))$ when this set is nonempty. It is a pair: its first component is the domain, and its second is the function. The properties of schemes give properties of the map.

| Lean name | Property of the scheme | Consequence |
|---|---|---|
| `CantorScheme.Disjoint.map_injective` | the children of each set are disjoint | the map is injective |
| `CantorScheme.VanishingDiam.map_continuous` | the diameters go to $0$ along each branch | the map is continuous |
| `CantorScheme.ClosureAntitone.map_of_vanishingDiam` | each child closure is in the parent, all sets nonempty, complete space | the domain is everything |

**Proposition** (`CantorScheme.VanishingDiam.map_continuous`). If $\beta$ is discrete and the diameters vanish along each branch, then the induced map is continuous.

*Proof.* Let $x$ be in the domain and let $\varepsilon > 0$. Choose $n$ with $\mathrm{diam}\, A(\mathrm{res}(x, n)) < \varepsilon$ (`CantorScheme.VanishingDiam.dist_lt`). The branches that agree with $x$ below $n$ form an open cylinder, and their images lie in the same set $A(\mathrm{res}(x, n))$ (`CantorScheme.map_mem`). So these images are at distance less than $\varepsilon$ from the image of $x$.

#### Perfect sets and the Cantor space

A set is perfect if it is closed and has no isolated point. The predicate `Perfect` and the splitting of a perfect set into two disjoint perfect sets are in the general topology library. In a metric space, `Perfect.small_diam_splitting` also makes the two parts of diameter at most $\varepsilon$.

**Theorem** (`Perfect.exists_nat_bool_injection`). A nonempty perfect set $C$ in a complete metric space contains the image of a continuous injective map from `ℕ → Bool`.

*Proof sketch.* Build a scheme $D$ indexed by `Bool` with `Perfect.small_diam_splitting`: $D([\,]) = C$, and the two children of $D(l)$ are disjoint nonempty perfect subsets of diameter at most $u_n$, with $u_n \to 0$. The scheme is disjoint, has vanishing diameter, and each child closure is in its parent. By the three lemmas of the table, the induced map is defined everywhere, continuous and injective.

With the Cantor-Bendixson theorem of the general library, `IsClosed.exists_nat_bool_injection_of_not_countable` follows: an uncountable closed set in a Polish space contains a copy of the Cantor space. So a closed set in a Polish space is countable or has the cardinality of the continuum.

The Cantor space also maps onto each compact metric space. The module `Mathlib.Topology.MetricSpace.HausdorffAlexandroff` gives the binary expansion `Real.fromBinary`, a continuous surjection from `ℕ → Bool` onto $[0, 1]$ (`Real.fromBinary_continuous`, `Real.fromBinary_surjective`). The map `cantorToHilbert` applies it to each coordinate of a homeomorphism from the Cantor space to its countable power, and so it is a continuous surjection onto the Hilbert cube (`cantorToHilbert_continuous`, `cantorToHilbert_surjective`).

**Theorem** (`exists_nat_bool_continuous_surjective_of_compact`). Each nonempty compact metric space $X$ is the image of a continuous map `(ℕ → Bool) → X`.

*Proof sketch.* By `Metric.PiNatEmbed.exists_embedding_to_hilbert_cube`, $X$ is homeomorphic to a subset $K$ of the Hilbert cube, and $K$ is closed because $X$ is compact. The preimage $K'$ of $K$ under `cantorToHilbert` is a nonempty closed subset of the Cantor space. By `exists_retractionCantorSet`, a form of `PiNat.exists_lipschitz_retraction_of_isClosed`, there is a continuous map from the Cantor space onto $K'$. Compose it with `cantorToHilbert` and with the inverse of the homeomorphism.

#### Common errors

1. `PiNat.metricSpace` and `PiCountable.metricSpace` are not global instances. Without `attribute [local instance] PiNat.metricSpace`, `dist` on `ℕ → ℕ` does not elaborate, or it finds another structure.
2. `PolishSpace α` holds no metric. Do not search for a `MetricSpace α` instance; use `TopologicalSpace.upgradeIsCompletelyMetrizable α` inside the proof.
3. `CantorScheme.inducedMap A` is a dependent pair. Its function `(CantorScheme.inducedMap A).2` takes a point of the domain, a subtype, and not a bare sequence.

### Exercises

1. (A) Compute `PiNat.firstDiff` and the distance between the sequences $(0, 1, 2, 3, \dots)$ and $(0, 1, 5, 3, \dots)$ in `ℕ → ℕ`.
2. (A) Show from `PiNat.dist_triangle_nonarch` that two cylinders are either disjoint or one is a subset of the other.
3. (A) Show that the set of irrational numbers in $\mathbb{R}$ is Polish, with `IsGδ.polishSpace`.
4. (B) Show that each nonempty closed subset of `ℕ → Bool` is the image of a continuous map from `ℕ → Bool`.
5. (B) Show that $[0, 1]$ is not homeomorphic to `ℕ → Bool`, but that it is a continuous image of it.
6. (C) Prove that a countable intersection of clopenable sets is clopenable.

### Reference

<?reference?>
