---
title: Gluing, the Kuratowski embedding and the Gromov-Hausdorff distance
kind: api
modules:
  - Mathlib.Topology.MetricSpace.Gluing
  - Mathlib.Topology.MetricSpace.Kuratowski
  - Mathlib.Topology.MetricSpace.GromovHausdorff
  - Mathlib.Topology.MetricSpace.GromovHausdorffRealized
  - Mathlib.Topology.MetricSpace.GromovProduct
explains:
  E2: [Metric.toGlue_commute, Metric.Sum.one_le_dist_inl_inr, KuratowskiEmbedding.embeddingOfSubset_isometry, kuratowskiEmbedding.isometry, GromovHausdorff.ghDist_le_hausdorffDist, GromovHausdorff.toGHSpace_eq_toGHSpace_iff_isometryEquiv, GromovHausdorff.ghDist_le_of_approx_subsets, GromovHausdorff.hausdorffDist_optimal, Metric.gromovProduct_add_gromovProduct₁₂]
  E1: auto
families: []
requires: [V04, V13.C01, V13.C02, V13.C03, V13.C05, V13.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Gluing, the Kuratowski embedding and the Gromov-Hausdorff distance

### Overview

The Hausdorff distance of Section 3 compares two subsets of one metric space. The Gromov-Hausdorff distance compares two metric spaces that need not lie in a common space. For nonempty compact metric spaces $X$ and $Y$, it is the infimum of the Hausdorff distances $d_H(\Phi(X), \Psi(Y))$ over all metric spaces $Z$ and all isometric embeddings $\Phi : X \to Z$ and $\Psi : Y \to Z$. Two compact spaces are at distance $0$ exactly when they are isometric, so the distance turns the set of isometry classes of compact metric spaces into a metric space. This space is complete and separable.

The definition quantifies over all metric spaces, and this is not a legal definition in type theory. The library solves the problem with two constructions, and this section describes them in order. The first is gluing: two spaces with a common part can be put in one space. The second is the Kuratowski embedding: each separable metric space embeds isometrically in the space $\ell^\infty$ of bounded real sequences. With these tools, all the embeddings in the definition can be taken in $\ell^\infty$, and the Gromov-Hausdorff space becomes a quotient of the nonempty compact subsets of $\ell^\infty$. The section ends with the Gromov product, a small notion of the same family.

### The library around it

#### Gluing two metric spaces

The module `Mathlib.Topology.MetricSpace.Gluing` starts with a square of isometries. Let $\Phi : Z \to X$ and $\Psi : Z \to Y$ be isometric embeddings, with $Z$ nonempty. The type `Metric.GlueSpace hΦ hΨ` is a metric space that contains copies of $X$ and $Y$ glued along the images of $Z$. The two maps `Metric.toGlueL hΦ hΨ : X → Metric.GlueSpace hΦ hΨ` and `Metric.toGlueR hΦ hΨ` are isometries (`Metric.toGlueL_isometry`, `Metric.toGlueR_isometry`).

The construction goes through a function on the disjoint union $X \oplus Y$. For $\varepsilon \in \mathbb{R}$, `Metric.glueDist Φ Ψ ε` keeps the distances inside $X$ and inside $Y$, and puts
$$d(x, y) = \inf_{p \in Z} \big( d(x, \Phi p) + d(y, \Psi p) \big) + \varepsilon$$
for $x \in X$ and $y \in Y$. A path from $x$ to $y$ must pass through the common part, and $\varepsilon$ is the cost of the passage. The lemma `Metric.glueDist_glued_points` says that $\Phi(p)$ and $\Psi(p)$ are at distance exactly $\varepsilon$, and `Metric.le_glueDist_inl_inr` says that no point of $X$ is closer than $\varepsilon$ to a point of $Y$. When $\varepsilon > 0$ and $\Phi$ and $\Psi$ distort distances by at most $2 \varepsilon$, the definition `Metric.glueMetricApprox` makes $X \oplus Y$ a metric space. When $\varepsilon = 0$, the points $\Phi(p)$ and $\Psi(p)$ have distance $0$, and `Metric.GlueSpace` is the quotient that identifies them.

**Proposition** (`Metric.toGlue_commute`). The square commutes: `Metric.toGlueL hΦ hΨ ∘ Φ = Metric.toGlueR hΦ hΨ ∘ Ψ`.

*Proof.* For $p \in Z$, the images of $\Phi(p)$ and $\Psi(p)$ in $X \oplus Y$ have glue distance $0$ by `Metric.glueDist_glued_points` with $\varepsilon = 0$. Points at distance $0$ become equal in the quotient metric space.

#### Disjoint unions and inductive limits

The same module puts a metric on $X \oplus Y$ for any nonempty metric spaces. The distance `Metric.Sum.dist` keeps the distances inside each part, and for $x \in X$, $y \in Y$ it is $d(x, x_0) + 1 + d(y_0, y)$, where $x_0$ and $y_0$ are fixed base points. The lemma `Metric.Sum.dist_eq_glueDist` identifies it with `Metric.glueDist` for the one-point space $Z$ and $\varepsilon = 1$.

**Proposition** (`Metric.Sum.one_le_dist_inl_inr`). For $x \in X$ and $y \in Y$, `1 ≤ Metric.Sum.dist (Sum.inl x) (Sum.inr y)`.

*Proof.* The distance is $d(x, x_0) + 1 + d(y_0, y)$, and the two outer terms are nonnegative.

So the two parts are open, and the topology of the metric is the topology of the disjoint union. The structure `Metric.metricSpaceSum` is a definition and not a global instance, because the choice of base points is arbitrary; a proof that needs it activates it as a local instance. With it, `Metric.isometry_inl` and `Metric.isometry_inr` hold, and `Metric.Sum.dist_eq` unfolds the distance. The family form for $\Sigma_i E_i$ is `Metric.Sigma.metricSpace`, with `Metric.Sigma.dist_same`, `Metric.Sigma.dist_ne`, `Metric.Sigma.isometry_mk`, `Metric.Sigma.fst_eq_of_dist_lt_one` (two points at distance less than $1$ lie in the same part) and `Metric.Sigma.completeSpace`.

The last construction is the inductive limit of a chain $X_0 \to X_1 \to X_2 \to \cdots$ of isometric embeddings $f_n$. The type `Metric.InductiveLimit I`, where `I` is the family of proofs that each $f_n$ is an isometry, is the increasing union of the $X_n$. The maps `Metric.toInductiveLimit I n` are isometries (`Metric.toInductiveLimit_isometry`) and they commute with the $f_n$ (`Metric.toInductiveLimit_commute`). The union of their ranges is dense (`Metric.dense_iUnion_range_toInductiveLimit`), so the limit of separable spaces is separable (`Metric.separableSpaceInductiveLimit_of_separableSpace`).

#### The Kuratowski embedding

Let $\alpha$ be a metric space and let $(x_n)$ be a sequence in $\alpha$. The map `KuratowskiEmbedding.embeddingOfSubset x` sends $a$ to the sequence
$$\big( d(a, x_n) - d(x_0, x_n) \big)_{n \in \mathbb{N}}.$$
By the triangle inequality each term has absolute value at most $d(a, x_0)$, so the sequence is bounded and lies in $\ell^\infty(\mathbb{N}, \mathbb{R})$, written `lp (fun _ ↦ ℝ) ⊤` in Lean. The subtraction of $d(x_0, x_n)$ is there only to make the sequence bounded.

**Proposition** (`KuratowskiEmbedding.embeddingOfSubset_isometry`). If $(x_n)$ is dense in $\alpha$, then `KuratowskiEmbedding.embeddingOfSubset x` is an isometry.

*Proof.* The $n$-th coordinate of the difference of the images of $a$ and $b$ is $d(a, x_n) - d(b, x_n)$. Its absolute value is at most $d(a, b)$, so the sup norm is at most $d(a, b)$; this half is `KuratowskiEmbedding.embeddingOfSubset_dist_le`. For the other half, let $\delta > 0$ and choose $x_n$ with $d(b, x_n) < \delta$, by density. Then $d(a, x_n) - d(b, x_n) \ge d(a, b) - 2\delta$. So the sup norm is at least $d(a, b) - 2 \delta$ for each $\delta > 0$.

A separable space has a dense sequence. The theorem `KuratowskiEmbedding.exists_isometric_embedding` gives an isometry from each separable metric space into $\ell^\infty$, and `kuratowskiEmbedding α` is a chosen one, with `kuratowskiEmbedding.isometry`. For a nonempty compact space, the image is a nonempty compact subset, `NonemptyCompacts.kuratowskiEmbedding α`. As a by-product, `LipschitzOnWith.extend_lp_infty` extends a $K$-Lipschitz map from a subset into $\ell^\infty$ to a $K$-Lipschitz map on the whole space, coordinate by coordinate.

#### The Gromov-Hausdorff space

The type `GromovHausdorff.GHSpace` is the quotient of the nonempty compact subsets of $\ell^\infty$ by the relation "isometric". For a nonempty compact metric space $X$, `GromovHausdorff.toGHSpace X` is the class of its Kuratowski image. In the other direction, `GromovHausdorff.GHSpace.Rep p` is a type that represents the class $p$, and `GromovHausdorff.GHSpace.toGHSpace_rep` says that its class is $p$.

**Theorem** (`GromovHausdorff.toGHSpace_eq_toGHSpace_iff_isometryEquiv`). For nonempty compact metric spaces, `toGHSpace X = toGHSpace Y` holds if and only if there is an isometric equivalence `X ≃ᵢ Y`.

*Proof sketch.* Both sides say that the Kuratowski images of $X$ and $Y$ are isometric. The image of $X$ is isometric to $X$ by `kuratowskiEmbedding.isometry`, and the same holds for $Y$. Compose the isometric equivalences.

The distance on `GromovHausdorff.GHSpace` is the infimum of the Hausdorff distances between representatives in $\ell^\infty$. The function `GromovHausdorff.ghDist X Y` is this distance between the classes of $X$ and $Y$, and `GromovHausdorff.dist_ghDist` gives the other direction. The definition uses only $\ell^\infty$, but the next result shows that any common space gives an upper bound.

**Proposition** (`GromovHausdorff.ghDist_le_hausdorffDist`). If $\Phi : X \to \gamma$ and $\Psi : Y \to \gamma$ are isometries into a metric space $\gamma$, then `ghDist X Y ≤ Metric.hausdorffDist (Set.range Φ) (Set.range Ψ)`.

*Proof sketch.* The space $\gamma$ need not be separable. Replace it by the closure of $\Phi(X) \cup \Psi(Y)$, which is separable because $X$ and $Y$ are compact, and embed it in $\ell^\infty$ by the Kuratowski embedding. The Hausdorff distance between the images does not change under an isometry, and the images are representatives of the classes of $X$ and $Y$.

The infimum is attained. The module `Mathlib.Topology.MetricSpace.GromovHausdorffRealized` builds a compact space `GromovHausdorff.OptimalGHCoupling X Y` (`GromovHausdorff.compactSpace_optimalGHCoupling`) with isometries `GromovHausdorff.optimalGHInjl X Y` and `GromovHausdorff.optimalGHInjr X Y` (`GromovHausdorff.isometry_optimalGHInjl`, `GromovHausdorff.isometry_optimalGHInjr`).

**Theorem** (`GromovHausdorff.hausdorffDist_optimal`). The Hausdorff distance between the ranges of `optimalGHInjl X Y` and `optimalGHInjr X Y` is `ghDist X Y`.

*Proof sketch.* A metric on $X \oplus Y$ that extends the metrics of $X$ and $Y$ is a function on $(X \oplus Y)^2$. The admissible functions with a bound on the cross distances form an equicontinuous and bounded family of functions on a compact space, so they form a compact set, by the theorem of Arzelà and Ascoli. The Hausdorff distance `GromovHausdorff.HD` of such a function is continuous, so it has a minimum on this compact set. The coupling is the metric space of a minimizer.

With an optimal coupling, the triangle inequality follows from gluing: glue an optimal coupling of $X$ and $Y$ to an optimal coupling of $Y$ and $Z$ along $Y$. The zero distance property follows too: if `ghDist X Y = 0`, the two ranges in the optimal coupling are compact sets at Hausdorff distance $0$, so they are equal, and $X$ and $Y$ are isometric. The instance `GromovHausdorff.instMetricSpaceGHSpace` records the result.

A computable upper bound uses approximate isometries.

**Proposition** (`GromovHausdorff.ghDist_le_of_approx_subsets`). Let $s \subseteq X$ be $\varepsilon_1$-dense, and let $\Phi : s \to Y$ have an $\varepsilon_3$-dense range and distort distances by at most $\varepsilon_2$. Then `ghDist X Y ≤ ε₁ + ε₂ / 2 + ε₃`.

*Proof sketch.* Glue $s$ to $Y$ along $\Phi$ with `Metric.glueMetricApprox` and $\varepsilon = \varepsilon_2/2$. In the glued space, each point of $s$ is at distance $\varepsilon_2/2$ from its image, so the Hausdorff distance between $X$ and $Y$ is at most $\varepsilon_1 + \varepsilon_2/2 + \varepsilon_3$. Apply `GromovHausdorff.ghDist_le_hausdorffDist`.

The space as a whole has good properties. It is complete (`GromovHausdorff.instCompleteSpaceGHSpace`) and second countable (`GromovHausdorff.instSecondCountableTopologyGHSpace`), so it is a Polish space in the sense of Section 5. The Gromov compactness criterion is `GromovHausdorff.totallyBounded`: a set of classes is totally bounded if the diameters are bounded by one constant $C$ and, for each $n$, each space is covered by $K(n)$ balls of radius $u(n)$, with $u(n) \to 0$. For a fixed space $X$, the map `TopologicalSpace.NonemptyCompacts.toGHSpace` from the nonempty compact subsets of $X$ is $1$-Lipschitz (`GromovHausdorff.toGHSpace_lipschitz`, `GromovHausdorff.ghDist_le_nonemptyCompacts_dist`), so it is continuous.

#### The Gromov product

In a pseudometric space, the Gromov product of $y$ and $z$ at the base point $x$ is
$$(y \mid z)_x = \tfrac{1}{2} \big( d(x, y) + d(x, z) - d(y, z) \big),$$
written `Metric.gromovProduct x y z`, with `Metric.gromovProduct_eq` as the definitional equation. It measures how long the paths from $x$ to $y$ and from $x$ to $z$ stay together. In a tree it is exactly the length of the common part. It is the basic tool of the theory of hyperbolic spaces. The library gives the elementary facts.

| Lean name | Statement |
|---|---|
| `Metric.gromovProduct_comm` | $(y \mid z)_x = (z \mid y)_x$ |
| `Metric.gromovProduct_nonneg` | $0 \le (y \mid z)_x$ |
| `Metric.gromovProduct_le_dist_left` | $(y \mid z)_x \le d(x, y)$ |
| `Metric.gromovProduct_le_dist_right` | $(y \mid z)_x \le d(x, z)$ |
| `Metric.gromovProduct_self` | $(y \mid y)_x = d(x, y)$ |
| `Metric.gromovProduct_self_left` | $(x \mid y)_x = 0$ |
| `Metric.gromovProduct_add_gromovProduct₁₂` | $(y \mid z)_x + (x \mid z)_y = d(x, y)$ |
| `Metric.gromovProduct_add_gromovProduct₁₃` | $(y \mid z)_x + (y \mid x)_z = d(x, z)$ |

**Proposition** (`Metric.gromovProduct_add_gromovProduct₁₂`). $(y \mid z)_x + (x \mid z)_y = d(x, y)$.

*Proof.* The sum is $\frac12 (d(x, y) + d(x, z) - d(y, z)) + \frac12 (d(y, x) + d(y, z) - d(x, z))$. The terms $d(x, z)$ and $d(y, z)$ cancel, and $d(y, x) = d(x, y)$, so the sum is $d(x, y)$.

The nonnegativity and the two upper bounds are the triangle inequality in another form.

#### Common errors

1. `Metric.metricSpaceSum` and `Metric.Sigma.metricSpace` are definitions, not global instances. A statement about the metric of `X ⊕ Y` needs `attribute [local instance] Metric.metricSpaceSum` or an explicit instance argument; otherwise `X ⊕ Y` has no metric.
2. `GromovHausdorff.ghDist` needs `[CompactSpace X]` and `[Nonempty X]` for both spaces. The empty space has no class in `GromovHausdorff.GHSpace`.
3. `GromovHausdorff.GHSpace.Rep p` is a type chosen by the axiom of choice. Two spaces with the same class are isometric, but not equal as types; transport a statement with an isometric equivalence, not with a rewrite.

### Exercises

1. (A) Show that the Gromov-Hausdorff distance between a one-point space and a compact space $X$ is at most the diameter of $X$, with `GromovHausdorff.ghDist_le_hausdorffDist` and an embedding of the point in $X$.
2. (A) Let $X = \{0, 1\}$ with $d(0, 1) = 1$ and $Y = \{0, 2\}$ with $d(0, 2) = 2$, as subsets of $\mathbb{R}$. Give an upper bound for `ghDist X Y` with `GromovHausdorff.ghDist_le_of_approx_subsets`.
3. (A) Prove `Metric.gromovProduct_le_dist_left` from `Metric.gromovProduct_eq` and the triangle inequality.
4. (B) Show that the spaces $\{0, 1/n, 2/n, \dots, 1\}$ converge to $[0, 1]$ in `GromovHausdorff.GHSpace`.
5. (B) Show that in a metric space that is a tree, such as $\mathbb{R}$, the Gromov product satisfies $(x \mid z)_w \ge \min((x \mid y)_w, (y \mid z)_w)$ for all points.
6. (C) Prove that the set of classes of compact metric spaces with at most $N$ points is closed in `GromovHausdorff.GHSpace`.

### Reference

<?reference?>
