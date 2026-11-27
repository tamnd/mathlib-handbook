---
title: Metric spaces and their topology
kind: theory
modules:
  - Mathlib.Topology.MetricSpace.Pseudo.Defs
  - Mathlib.Topology.MetricSpace.Defs
  - Mathlib.Topology.MetricSpace.Pseudo.Constructions
  - Mathlib.Topology.EMetricSpace.Defs
  - Mathlib.Topology.Bornology.Basic
explains:
  E3: [PseudoMetricSpace, MetricSpace, Metric.ball, EMetricSpace]
  E2: [Dist, dist_self, dist_comm, dist_triangle, dist_nonneg, dist_eq_zero, Metric.mem_ball, Metric.closedBall, Metric.sphere, Metric.isOpen_ball, Metric.isOpen_iff, Metric.nhds_basis_ball, Metric.mem_nhds_iff, Metric.eventually_nhds_iff, Metric.mem_closure_iff, Metric.continuous_iff, Metric.continuousAt_iff, Metric.tendsto_nhds, Real.dist_eq, Bornology.IsBounded, Metric.isBounded_iff, Prod.pseudoMetricSpaceMax, Prod.dist_eq, Subtype.pseudoMetricSpace, PseudoEMetricSpace, EDist]
  E1: auto
families: []
requires: [V02, V04, V13.C01, V13.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Metric spaces and their topology

### Overview

A metric on a set is a distance function that satisfies the triangle inequality. Each metric gives a topology, whose open sets are the sets that contain a ball around each of their points. In this topology the neighbourhood filter of a point has the balls as a basis, and so each filter statement of Chapter 2 has an $\varepsilon$ form.

Mathlib makes three choices that a student must know. First, the basic class is the pseudometric space, which allows distance $0$ between distinct points; a metric space is a pseudometric space with one more axiom. Second, a metric space carries its topology as data, and also a uniform structure (Chapter 7) and a bornology, the family of bounded sets. Third, the distance on a product is the maximum of the distances, not the Euclidean distance.

### Definitions

**Definition (Metric space).** A pseudometric on a set $X$ is a map $d : X \times X \to \mathbb{R}$ such that for all $x, y, z \in X$:

1. $d(x, x) = 0$;
2. $d(x, y) = d(y, x)$;
3. $d(x, z) \le d(x, y) + d(y, z)$.

It is a metric if also $d(x, y) = 0$ implies $x = y$.

*Remarks.* The axioms give $d(x, y) \ge 0$: by 3, 2 and 1, $0 = d(x, x) \le d(x, y) + d(y, x) = 2 d(x, y)$. So nonnegativity is not an axiom. An extended metric takes values in $[0, \infty]$. It permits points at infinite distance, as in the space of all functions $\mathbb{N} \to \mathbb{R}$ with the sup distance.

::: mathlib
`PseudoMetricSpace` · `Mathlib.Topology.MetricSpace.Pseudo.Defs`

The class has the field `dist` from the class `Dist`, the axioms `dist_self`, `dist_comm` and `dist_triangle`, and three more fields: an extended distance `edist`, a uniform structure `toUniformSpace` and a bornology `toBornology`, each with a proof that it agrees with `dist`. The extra fields are there so that a product or a subtype gets a topology equal by definition to the topology from its own instances. When a user builds an instance, the extra fields have default values.

<?decl PseudoMetricSpace?>
:::

::: mathlib
`MetricSpace` · `Mathlib.Topology.MetricSpace.Defs`

A metric space extends a pseudometric space with `eq_of_dist_eq_zero`. The lemma `dist_eq_zero` states `dist x y = 0 ↔ x = y`.

<?decl MetricSpace?>
:::

::: mathlib
`dist_triangle` · `Mathlib.Topology.MetricSpace.Pseudo.Defs`

The triangle inequality, `dist x z ≤ dist x y + dist y z`. Its variants `dist_triangle_left` and `dist_triangle_right` permute the points.

<?decl dist_triangle?>
:::

::: mathlib
`dist_nonneg` · `Mathlib.Topology.MetricSpace.Pseudo.Defs`

The distance is nonnegative, by the proof in the remarks.

<?decl dist_nonneg?>
:::

::: mathlib
`Real.dist_eq` · `Mathlib.Topology.MetricSpace.Pseudo.Defs`

On `ℝ` the distance is `|x - y|`.

<?decl Real.dist_eq?>
:::

**Definition (Balls).** Let $(X, d)$ be a pseudometric space, $x \in X$ and $r \in \mathbb{R}$. The open ball is $B(x, r) = \{y : d(y, x) < r\}$, the closed ball is $\bar B(x, r) = \{y : d(y, x) \le r\}$, and the sphere is $S(x, r) = \{y : d(y, x) = r\}$.

::: mathlib
`Metric.ball` · `Mathlib.Topology.MetricSpace.Pseudo.Defs`

`ball x ε = {y | dist y x < ε}`. Note the order `dist y x`. The lemma `mem_ball` unfolds membership. A ball of radius `ε ≤ 0` is empty, and no positivity hypothesis is needed to form it.

<?decl Metric.ball?>
:::

::: mathlib
`Metric.closedBall` · `Mathlib.Topology.MetricSpace.Pseudo.Defs`

The closed ball. It is closed by `Metric.isClosed_closedBall`. In a general metric space it need not be the closure of the open ball.

<?decl Metric.closedBall?>
:::

**Definition (Metric topology).** A set $U \subseteq X$ is open for $d$ if for each $x \in U$ there is an $\varepsilon > 0$ with $B(x, \varepsilon) \subseteq U$.

**Definition (Bounded set).** A set $A \subseteq X$ is bounded if there is a $C$ with $d(x, y) \le C$ for all $x, y \in A$.

::: mathlib
`Bornology.IsBounded` · `Mathlib.Topology.Bornology.Basic`

Mathlib defines boundedness through a bornology, a family of "bounded" sets closed under subsets and finite unions. A pseudometric space carries the bornology of the metrically bounded sets, and `Metric.isBounded_iff` gives the definition of the text. The bornology lets one notion of boundedness serve metric spaces and other structures.

<?decl Bornology.IsBounded?>
:::

::: mathlib
`Metric.isBounded_iff` · `Mathlib.Topology.MetricSpace.Pseudo.Defs`

A set is bounded if the distances between its points are bounded.

<?decl Metric.isBounded_iff?>
:::

### Theorems and proofs

**Theorem (The metric topology).** The open sets of a pseudometric space form a topology. Each open ball is open, and for each $x$ the balls $B(x, \varepsilon)$ with $\varepsilon > 0$ form a basis of $\mathcal{N}(x)$.

*Proof.* The sets $\emptyset$ and $X$ are open. If each $U_i$ is open and $x \in \bigcup U_i$, then $x \in U_j$ for some $j$, and a ball around $x$ in $U_j$ lies in the union. If $U, V$ are open and $x \in U \cap V$, choose $B(x, \varepsilon) \subseteq U$ and $B(x, \varepsilon') \subseteq V$; then $B(x, \min(\varepsilon, \varepsilon')) \subseteq U \cap V$.

Let $y \in B(x, r)$ and $\varepsilon = r - d(y, x) > 0$. For $z \in B(y, \varepsilon)$, the triangle inequality gives $d(z, x) \le d(z, y) + d(y, x) < \varepsilon + d(y, x) = r$. So $B(y, \varepsilon) \subseteq B(x, r)$, and $B(x, r)$ is open.

Each ball $B(x, \varepsilon)$ with $\varepsilon > 0$ is open and contains $x$, so it is a neighbourhood of $x$. If $N$ is a neighbourhood of $x$, then $N$ contains an open $U$ with $x \in U$, and $U$ contains some $B(x, \varepsilon)$. $\square$

::: mathlib
`Metric.isOpen_iff` · `Mathlib.Topology.MetricSpace.Pseudo.Defs`

The definition of the metric topology as a theorem. In Mathlib the topology comes from the uniform structure, and this lemma is proved from it.

<?decl Metric.isOpen_iff?>
:::

::: mathlib
`Metric.isOpen_ball` · `Mathlib.Topology.MetricSpace.Pseudo.Defs`

An open ball is open.

<?decl Metric.isOpen_ball?>
:::

::: mathlib
`Metric.nhds_basis_ball` · `Mathlib.Topology.MetricSpace.Pseudo.Defs`

`(𝓝 x).HasBasis (fun ε ↦ 0 < ε) (ball x)`. With `Filter.HasBasis.tendsto_iff` of Chapter 2, it gives each $\varepsilon$-$\delta$ statement below. The lemmas `Metric.mem_nhds_iff` and `Metric.eventually_nhds_iff` are its two direct forms.

<?decl Metric.nhds_basis_ball?>
:::

::: mathlib
`Metric.mem_nhds_iff` · `Mathlib.Topology.MetricSpace.Pseudo.Defs`

A set is a neighbourhood of `x` if it contains a ball around `x`.

<?decl Metric.mem_nhds_iff?>
:::

::: mathlib
`Metric.eventually_nhds_iff` · `Mathlib.Topology.MetricSpace.Pseudo.Defs`

A property holds near `x` if it holds at each `y` with `dist y x < ε`, for some `ε > 0`.

<?decl Metric.eventually_nhds_iff?>
:::

**Theorem ($\varepsilon$-$\delta$ forms).** Let $X$ and $Y$ be pseudometric spaces, $f : X \to Y$, $a \in X$, $b \in Y$ and $A \subseteq X$.

1. $\mathrm{Tendsto}\ f\ \mathcal{N}(a)\ \mathcal{N}(b)$ if and only if for each $\varepsilon > 0$ there is a $\delta > 0$ with $d(f(x), b) < \varepsilon$ whenever $d(x, a) < \delta$.
2. $f$ is continuous if and only if for each $a$ and each $\varepsilon > 0$ there is a $\delta > 0$ with $d(f(x), f(a)) < \varepsilon$ whenever $d(x, a) < \delta$.
3. $a \in \overline{A}$ if and only if for each $\varepsilon > 0$ there is a $y \in A$ with $d(a, y) < \varepsilon$.

*Proof.* (1) By the basis criterion for `Tendsto` with the bases of balls of $\mathcal{N}(a)$ and $\mathcal{N}(b)$, the statement says that for each $\varepsilon > 0$ there is a $\delta > 0$ with $f(B(a, \delta)) \subseteq B(b, \varepsilon)$.

(2) By Chapter 2, $f$ is continuous if and only if it tends to $\mathcal{N}(f(a))$ along $\mathcal{N}(a)$ for each $a$. Apply 1 with $b = f(a)$.

(3) By Chapter 2, $a \in \overline{A}$ if and only if each neighbourhood of $a$ meets $A$. Since the balls form a basis of $\mathcal{N}(a)$, this holds if and only if each ball $B(a, \varepsilon)$ meets $A$. $\square$

::: mathlib
`Metric.tendsto_nhds` · `Mathlib.Topology.MetricSpace.Pseudo.Defs`

For a general source filter: `Tendsto u f (𝓝 a) ↔ ∀ ε > 0, ∀ᶠ x in f, dist (u x) a < ε`. This form is often the most convenient.

<?decl Metric.tendsto_nhds?>
:::

::: mathlib
`Metric.continuousAt_iff` · `Mathlib.Topology.MetricSpace.Pseudo.Defs`

Continuity at a point in $\varepsilon$-$\delta$ form.

<?decl Metric.continuousAt_iff?>
:::

::: mathlib
`Metric.continuous_iff` · `Mathlib.Topology.MetricSpace.Pseudo.Defs`

Part 2 of the theorem.

<?decl Metric.continuous_iff?>
:::

::: mathlib
`Metric.mem_closure_iff` · `Mathlib.Topology.MetricSpace.Pseudo.Defs`

Part 3 of the theorem.

<?decl Metric.mem_closure_iff?>
:::

**Theorem (Products).** Let $(X, d_X)$ and $(Y, d_Y)$ be pseudometric spaces and $d((x, y), (x', y')) = \max(d_X(x, x'), d_Y(y, y'))$. Then $d$ is a pseudometric on $X \times Y$, and its topology is the product topology.

*Proof.* The axioms 1 and 2 are clear. For 3, $d_X(x, x'') \le d_X(x, x') + d_X(x', x'') \le d((x,y),(x',y')) + d((x',y'),(x'',y''))$, and the same for $d_Y$; take the maximum. The ball for $d$ is a product of balls: $B((x, y), r) = B(x, r) \times B(y, r)$. A product of balls is open in the product topology, and each open box $U \times V$ that contains $(x, y)$ contains $B(x, r) \times B(y, r)$ with $r$ the smaller of the two radii for $U$ and $V$. So the two topologies have the same neighbourhood filters, and they are equal. $\square$

::: mathlib
`Prod.pseudoMetricSpaceMax` · `Mathlib.Topology.MetricSpace.Pseudo.Constructions`

The instance on `α × β` uses the max distance, `Prod.dist_eq`. The same holds for finite products `(i : ι) → α i`, with the sup distance. As a consequence, the distance on `ℝ × ℝ` and on `Fin 2 → ℝ` is not the Euclidean distance. The Euclidean space is the separate type `EuclideanSpace ℝ (Fin n)`, in the volume on inner product spaces.

<?decl Prod.pseudoMetricSpaceMax?>
:::

::: mathlib
`Prod.dist_eq` · `Mathlib.Topology.MetricSpace.Pseudo.Constructions`

The distance on a product is the maximum of the two distances.

<?decl Prod.dist_eq?>
:::

::: mathlib
`Subtype.pseudoMetricSpace` · `Mathlib.Topology.MetricSpace.Pseudo.Constructions`

A subtype gets the restricted distance. Its topology is the subspace topology of Chapter 1, by definition of the instance through `PseudoMetricSpace.induced`.

<?decl Subtype.pseudoMetricSpace?>
:::

### Examples

**Example (The discrete metric).** On any set put $d(x, y) = 1$ for $x \ne y$ and $d(x, x) = 0$. The ball $B(x, 1/2)$ is $\{x\}$, so each set is open, and the topology is discrete. The closed ball $\bar B(x, 1)$ is the whole space, while the closure of $B(x, 1) = \{x\}$ is $\{x\}$. So a closed ball need not be the closure of the open ball with the same radius.

**Example (A pseudometric that is not a metric).** On $\mathbb{R}^2$ put $d((x, y), (x', y')) = |x - x'|$. It satisfies 1 to 3, but $d((0, 0), (0, 1)) = 0$. The open sets are the sets $U \times \mathbb{R}$ with $U$ open in $\mathbb{R}$. The topology is not $T_0$ (Chapter 4): the points $(0, 0)$ and $(0, 1)$ have the same neighbourhoods.

**Counterexample (The cofinite topology is not metrizable).** Let $X$ be infinite with the cofinite topology. Two nonempty open sets $X \setminus F$ and $X \setminus G$, with $F$ and $G$ finite, meet, since $X$ is not the finite set $F \cup G$. In a metric space two distinct points $x$ and $y$ have the disjoint balls $B(x, r)$ and $B(y, r)$ with $r = d(x, y)/2$. So no metric on $X$ gives the cofinite topology.

**Example (Extended metrics).** On the set of all bounded and unbounded sequences $\mathbb{N} \to \mathbb{R}$, the value $\sup_n |u_n - v_n|$ can be $\infty$. It is an extended metric, and the predicate "at finite distance" is an equivalence relation whose classes are open.

::: mathlib
`EMetricSpace` · `Mathlib.Topology.EMetricSpace.Defs`

The class of extended metric spaces, with `edist : α → α → ℝ≥0∞`. Each metric space is an extended metric space with `edist x y = ENNReal.ofReal (dist x y)`. Several results, such as the Baire theorem and the theory of Lipschitz maps, are proved once for extended metrics.

<?decl EMetricSpace?>
:::

::: mathlib
`PseudoEMetricSpace` · `Mathlib.Topology.EMetricSpace.Defs`

The extended pseudometric spaces, the base class of the hierarchy.

<?decl PseudoEMetricSpace?>
:::

### The library around it

The classes are in `Mathlib.Topology.MetricSpace.Pseudo.Defs`, `Mathlib.Topology.MetricSpace.Defs` and `Mathlib.Topology.EMetricSpace.Defs`. The hierarchy is: `PseudoEMetricSpace` below `PseudoMetricSpace` and `EMetricSpace`, which are both below `MetricSpace`. The names of the balls and the metric lemmas live in the namespace `Metric`, so a file writes `open Metric` to use `ball` and `closedBall` without prefix. The extended analogues live in `EMetric`.

To build a metric space instance on a new type, give `dist` and the axioms; the defaults fill the topology and the uniformity. When a type already has a topology, an instance that forgets it creates two different topologies. The fix is to replace the fields with the existing ones, using `PseudoMetricSpace.replaceTopology` or `PseudoMetricSpace.replaceUniformity`.

The reference table at the end of the section lists the declarations of the modules.

### Exercises

1. (A) Show that $|d(x, z) - d(y, z)| \le d(x, y)$, and deduce that $x \mapsto d(x, z)$ is continuous.
2. (A) Show that closed balls are closed, and that the sphere $S(x, r)$ is closed.
3. (A) Show that in $\mathbb{R}$ the closure of $B(x, r)$ is $\bar B(x, r)$ for $r > 0$.
4. (B) Show that $d'(x, y) = \min(d(x, y), 1)$ is a metric with the same topology as $d$. Deduce that boundedness is not a topological property.
5. (B) Show that each metric space is first countable, and that a separable metric space is second countable.
6. (B) Show that the max distance, the sum distance $d_X + d_Y$ and the Euclidean distance on $X \times Y$ give the same topology.
7. (C) Let $X$ be a pseudometric space and $x \sim y$ if $d(x, y) = 0$. Show that $\sim$ is an equivalence relation and that $d$ induces a metric on $X/{\sim}$ whose topology is the quotient topology.

### Notes and history

Metric spaces were defined by Fréchet in his thesis of 1906, under the name "classes (E)", and named by Hausdorff in 1914. The choice of the max distance on products in Mathlib makes the product of metric spaces agree, as a uniform space, with the product of uniform spaces by definition, and it works for each finite product in the same way. The extra fields of `PseudoMetricSpace` are the "forgetful inheritance" pattern of Mathlib: a structure that determines another one carries it as a field, with a proof of agreement, so that two paths through the class hierarchy give equal instances by definition.

### Reference

<?reference?>
