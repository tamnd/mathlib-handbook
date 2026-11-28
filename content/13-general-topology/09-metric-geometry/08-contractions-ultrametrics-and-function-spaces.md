---
title: Contractions, ultrametric spaces, snowflakes and metrics on function spaces
kind: api
modules:
  - Mathlib.Topology.MetricSpace.Contracting
  - Mathlib.Topology.MetricSpace.Ultra.Basic
  - Mathlib.Topology.MetricSpace.Ultra.Pi
  - Mathlib.Topology.MetricSpace.Ultra.ContinuousMaps
  - Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
  - Mathlib.Topology.MetricSpace.Snowflaking
  - Mathlib.Topology.MetricSpace.UniformConvergence
  - Mathlib.Topology.MetricSpace.Equicontinuity
explains:
  E2: [ContractingWith.dist_inequality, ContractingWith.exists_fixedPoint, ContractingWith.fixedPoint_unique, ContractingWith.apriori_dist_iterate_fixedPoint_le, IsUltrametricDist.ball_eq_of_mem, IsUltrametricDist.isClopen_ball, IsUltrametricDist.dist_eq_max_of_dist_ne_dist, Metric.Snowflaking.dist_toSnowflaking_toSnowflaking, UniformFun.edist_def, Metric.equicontinuousAt_iff]
  E1: auto
families: []
requires: [V04, V13.C01, V13.C02, V13.C03, V13.C05, V13.C06, V13.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Contractions, ultrametric spaces, snowflakes and metrics on function spaces

### Overview

This section collects four short topics of metric geometry. Each of them changes one feature of the distance and studies the effect.

The first topic is the contraction principle of Banach. A map that shrinks all distances by a factor $K < 1$ on a complete space has exactly one fixed point, and the iterates of each point converge to it at a geometric rate. The second topic is the ultrametric spaces, where the triangle inequality is replaced by the stronger inequality $d(x, z) \le \max(d(x, y), d(y, z))$. The $p$-adic numbers are the main example, and their balls behave in a way that is strange at first: each point of a ball is a centre, and each ball is open and closed. The third topic is the snowflake of a metric, the metric $d^\alpha$ for $0 < \alpha \le 1$. It has the same topology and the same uniform structure, but other Lipschitz maps and another dimension. The fourth topic is the extended metric of uniform convergence on a space of functions, and the $\varepsilon$-$\delta$ form of equicontinuity.

The section uses the extended metric spaces and complete spaces of Chapters 3 and 7, the clopen sets and total separation of Chapter 6, and the Lipschitz maps of Chapter 3.

### The library around it

#### Contracting maps

The predicate `ContractingWith K f`, for an extended metric space $\alpha$, $K \in \mathbb{R}_{\ge 0}$ and $f : \alpha \to \alpha$, is the conjunction $K < 1$ and `LipschitzWith K f`. The lemma `ContractingWith.toLipschitzWith` extracts the second half, and `ContractingWith.one_sub_K_pos` gives $0 < 1 - K$, the denominator of all the bounds below. The first estimate holds without completeness.

**Proposition** (`ContractingWith.dist_inequality`). In a metric space, for all $x, y$,
$$d(x, y) \le \frac{d(x, f x) + d(y, f y)}{1 - K}.$$

*Proof.* By the triangle inequality, $d(x, y) \le d(x, f x) + d(f x, f y) + d(f y, y) \le d(x, f x) + K d(x, y) + d(y, f y)$. Move $K d(x, y)$ to the left side and divide by $1 - K > 0$.

With $x$ and $y$ fixed points, the right side is $0$. So a contraction has at most one fixed point.

**Theorem** (`ContractingWith.exists_fixedPoint`). Let $\alpha$ be a complete extended metric space, let $f$ be `ContractingWith K f`, and let $x$ satisfy $\operatorname{edist}(x, f x) < \infty$. Then there is a fixed point $y$ of $f$ such that $f^n(x) \to y$ and
$$\operatorname{edist}(f^n x, y) \le \frac{\operatorname{edist}(x, f x) \, K^n}{1 - K}$$
for all $n$.

*Proof sketch.* By induction, $\operatorname{edist}(f^n x, f^{n+1} x) \le K^n \operatorname{edist}(x, f x)$. A geometric sum bounds $\operatorname{edist}(f^n x, f^m x)$ for $n \le m$ by $K^n \operatorname{edist}(x, f x)/(1 - K)$, so the sequence of iterates is Cauchy. By completeness it converges to some $y$. A Lipschitz map is continuous, so $f(y) = \lim f^{n+1}(x) = y$. Let $m \to \infty$ in the Cauchy bound to get the estimate.

The hypothesis $\operatorname{edist}(x, f x) < \infty$ is needed only in an extended metric space. The space may split into pieces at infinite distance from each other, and each piece has its own fixed point. The definition `ContractingWith.efixedPoint` chooses the fixed point that the theorem gives for $x$, with `ContractingWith.efixedPoint_isFixedPt`, `ContractingWith.tendsto_iterate_efixedPoint` and `ContractingWith.efixedPoint_eq_of_edist_lt_top`, which says that two points at finite distance give the same fixed point. The primed forms, such as `ContractingWith.exists_fixedPoint'` and `ContractingWith.efixedPoint'`, work with a complete subset $s$ with $f(s) \subseteq s$, on which only the restriction of $f$ contracts.

In a nonempty complete metric space, the fixed point is a total function of the map. The table gives the API.

| Lean name | Statement |
|---|---|
| `ContractingWith.fixedPoint f hf` | the fixed point of $f$ |
| `ContractingWith.fixedPoint_isFixedPt` | $f(p) = p$ for $p$ the fixed point |
| `ContractingWith.fixedPoint_unique` | each fixed point equals `ContractingWith.fixedPoint f hf` |
| `ContractingWith.tendsto_iterate_fixedPoint` | $f^n(x) \to p$ for every $x$ |
| `ContractingWith.dist_fixedPoint_le` | $d(x, p) \le d(x, f x)/(1 - K)$ |
| `ContractingWith.apriori_dist_iterate_fixedPoint_le` | $d(f^n x, p) \le d(x, f x) K^n/(1 - K)$ |
| `ContractingWith.aposteriori_dist_iterate_fixedPoint_le` | $d(f^n x, p) \le d(f^n x, f^{n+1} x)/(1 - K)$ |
| `ContractingWith.fixedPoint_lipschitz_in_map` | if $d(f z, g z) \le C$ for all $z$, the fixed points of $f$ and $g$ are at distance at most $C/(1 - K)$ |
| `ContractingWith.isFixedPt_fixedPoint_iterate` | if $f^n$ contracts, the fixed point of $f^n$ is a fixed point of $f$ |

**Proposition** (`ContractingWith.fixedPoint_unique`). If $f(x) = x$, then $x$ is `ContractingWith.fixedPoint f hf`.

*Proof.* Let $p$ be the chosen fixed point. Apply `ContractingWith.dist_inequality` to $x$ and $p$: the right side is $0$, so $d(x, p) = 0$ and $x = p$.

The a priori bound `ContractingWith.apriori_dist_iterate_fixedPoint_le` is the theorem above in the metric form. It tells in advance how many iterations give a required precision. The a posteriori bound uses only the last step, and it follows from `ContractingWith.dist_fixedPoint_le` applied at $f^n x$. The lemma `ContractingWith.fixedPoint_lipschitz_in_map` says that the fixed point depends continuously on the map. Later volumes use the contraction principle in the proofs of the inverse function theorem and of the theorem of Picard and Lindelöf.

#### Ultrametric spaces

The class `IsUltrametricDist X`, for a type with a distance, asks the strong triangle inequality. The constructor `IsUltrametricDist.mk` takes it as its only field, and the lemma `dist_triangle_max` states it: $d(x, z) \le \max(d(x, y), d(y, z))$. The class is a mixin on top of `PseudoMetricSpace`, in the same way as `CompleteSpace`. Its instances are subtypes (`IsUltrametricDist.subtype`), finite products with the sup distance (`Pi.instIsUltrametricDist`), and the space $C(X, Y)$ of continuous maps from a compact space to an ultrametric space with the sup distance (`ContinuousMap.isUltrametricDist`).

The strong inequality makes all triangles isosceles.

**Proposition** (`IsUltrametricDist.dist_eq_max_of_dist_ne_dist`). If $d(x, y) \ne d(y, z)$, then $d(x, z) = \max(d(x, y), d(y, z))$.

*Proof.* Assume $d(x, y) < d(y, z)$; the other case is symmetric. The strong inequality gives $d(x, z) \le d(y, z)$. It also gives $d(y, z) \le \max(d(y, x), d(x, z))$. The maximum is not $d(x, y)$, because $d(x, y) < d(y, z)$, so $d(y, z) \le d(x, z)$.

**Proposition** (`IsUltrametricDist.ball_eq_of_mem`). If $y \in B(x, r)$, then $B(x, r) = B(y, r)$.

*Proof.* Let $z \in B(x, r)$. Then $d(y, z) \le \max(d(y, x), d(x, z)) < r$, so $z \in B(y, r)$. The other inclusion is the same argument with $x$ and $y$ exchanged, since $x \in B(y, r)$.

So each point of a ball is a centre of the ball, and two balls of the same radius are equal or disjoint (`IsUltrametricDist.ball_eq_or_disjoint`). For balls of any radii, `IsUltrametricDist.ball_subset_trichotomy` says that one contains the other or they are disjoint. The closed forms are `IsUltrametricDist.closedBall_eq_of_mem`, `IsUltrametricDist.closedBall_eq_or_disjoint` and `IsUltrametricDist.closedBall_subset_trichotomy`.

**Proposition** (`IsUltrametricDist.isClopen_ball`). Each open ball is closed.

*Proof.* Let $y$ be outside $B(x, r)$. If $B(y, r)$ met $B(x, r)$ at a point $z$, then $B(y, r) = B(z, r) = B(x, r)$ by the previous proposition, so $y \in B(x, r)$. Hence $B(y, r)$ is a neighbourhood of $y$ outside $B(x, r)$, and the complement of $B(x, r)$ is open.

The closed balls and the spheres of nonzero radius are also clopen when the radius is not $0$ (`IsUltrametricDist.isClopen_closedBall`, `IsUltrametricDist.isClopen_sphere`). So the frontier of a ball is empty (`IsUltrametricDist.frontier_ball_eq_empty`). The clopen balls separate points, and the module `Mathlib.Topology.MetricSpace.Ultra.TotallySeparated` gives the instance `instTotallySeparatedSpaceOfIsUltrametricDist`: an ultrametric metric space is totally separated, so in particular totally disconnected.

#### Snowflakes

Let $X$ be a (pseudo, extended) metric space and let $0 < \alpha \le 1$. The function $d^\alpha$ is again a metric: for $0 < \alpha \le 1$ the map $t \mapsto t^\alpha$ is increasing, concave and $0$ at $0$, so it is subadditive, and the triangle inequality survives. The type `Metric.Snowflaking X α hα₀ hα₁` is a one-field structure around $X$ with this distance. The two proofs $0 < \alpha$ and $\alpha \le 1$ are part of the type, so the instance search can find the metric.

**Proposition** (`Metric.Snowflaking.dist_toSnowflaking_toSnowflaking`). For $x, y \in X$, the distance of their images in the snowflake is $d(x, y)^\alpha$.

The maps between $X$ and its snowflake follow the pattern of the type synonyms of the library. The equivalence `Metric.Snowflaking.toSnowflaking : X ≃ Metric.Snowflaking X α hα₀ hα₁` goes in, and `Metric.Snowflaking.ofSnowflaking` goes out. The simp lemmas `Metric.Snowflaking.toSnowflaking_ofSnowflaking` and `Metric.Snowflaking.ofSnowflaking_toSnowflaking` cancel them. The extended form of the distance is `Metric.Snowflaking.edist_toSnowflaking_toSnowflaking`.

The snowflake changes the distance but not the topology, the uniform structure or the bounded sets. The homeomorphism `Metric.Snowflaking.homeomorph` and the uniform equivalence `Metric.Snowflaking.uniformEquiv` with $X$ record the first two facts. The lemmas `Metric.Snowflaking.isBounded_image_toSnowflaking_iff` and `Metric.Snowflaking.isBounded_preimage_ofSnowflaking_iff` record the third. Balls go to balls with the radius raised to the power $\alpha$: `Metric.Snowflaking.image_toSnowflaking_ball` gives $B(x, r) \mapsto B(x, r^\alpha)$, and the same holds for closed balls and diameters (`Metric.Snowflaking.image_toSnowflaking_closedBall`, `Metric.Snowflaking.ediam_image_toSnowflaking`). The instances `Metric.Snowflaking.instMetricSpace`, `Metric.Snowflaking.instT2Space` and `Metric.Snowflaking.instSecondCountableTopology` transfer the structure.

A map that is Lipschitz for $d^\alpha$ is Hölder of exponent $\alpha$ for $d$, so the snowflake turns Hölder maps into Lipschitz maps. Its Hausdorff dimension is the dimension of $X$ divided by $\alpha$. This is how the von Koch snowflake gets its dimension $\log 4/\log 3$.

#### The extended metric of uniform convergence

Chapter 7 gives the type `UniformFun α β` of functions $\alpha \to \beta$ with the uniformity of uniform convergence. When $\beta$ is an extended pseudometric space, this uniformity comes from an extended pseudometric.

**Proposition** (`UniformFun.edist_def`). For $f, g$ in `UniformFun α β`, the distance is the sup distance
$$\operatorname{edist}(f, g) = \sup_{x \in \alpha} \operatorname{edist}(f(x), g(x)).$$

The instance `UniformFun.instPseudoEMetricSpace` gives this structure, and `UniformFun.instEMetricSpace` gives the separated form. The value can be $\infty$ for unbounded functions, so the result is an extended metric. For a bounded target, `UniformFun.instBoundedSpace` and `UniformFun.instPseudoMetricSpaceOfBoundedSpace` give a real pseudometric, with `UniformFun.dist_def`. The working lemmas are `UniformFun.edist_le` (the distance is at most $C$ if and only if each value is) and `UniformFun.edist_eval_le` (evaluation at a point is $1$-Lipschitz). The isometries `UniformFun.isometry_ofFun_boundedContinuousFunction` and `UniformFun.isometry_ofFun_continuousMap` compare this metric with the sup metric on bounded continuous functions and on $C(X, Y)$ for compact $X$.

For uniform convergence on a family $\mathfrak{S}$ of subsets, `UniformOnFun α β 𝔖`, the metric $\sup_{x \in \bigcup \mathfrak{S}} \operatorname{edist}(f(x), g(x))$ induces the uniformity only when $\mathfrak{S}$ is finite. So the instance `UniformOnFun.instEDistOfFiniteElemSet` asks `Finite 𝔖`. Its value is `UniformOnFun.edist_def`, and `UniformOnFun.edist_eq_restrict_sUnion` reduces it to `UniformFun` on $\bigcup \mathfrak{S}$. Lipschitz families are handled by `UniformFun.lipschitzWith_iff`: a map into `UniformFun α β` is $K$-Lipschitz if and only if each of its evaluations is.

#### Equicontinuity in metric spaces

Chapter 7 defines `EquicontinuousAt F x₀` and `UniformEquicontinuous F` with entourages. The module `Mathlib.Topology.MetricSpace.Equicontinuity` gives the metric forms.

**Proposition** (`Metric.equicontinuousAt_iff`). A family $F_i : \beta \to \alpha$ of maps between pseudometric spaces is equicontinuous at $x_0$ if and only if for each $\varepsilon > 0$ there is $\delta > 0$ such that $d(x, x_0) < \delta$ implies $d(F_i x_0, F_i x) < \varepsilon$ for all $i$.

*Proof.* The balls $B(x_0, \delta)$ form a basis of the neighbourhoods of $x_0$, and the sets $\{(a, b) : d(a, b) < \varepsilon\}$ form a basis of the uniformity of $\alpha$. Insert these bases into the definition of `EquicontinuousAt`.

The uniform form is `Metric.uniformEquicontinuous_iff`, and `Metric.equicontinuousAt_iff_pair` uses two points near $x_0$. A common modulus of continuity gives equicontinuity: if $b(t) \to 0$ as $t \to 0$ and $d(F_i x, F_i y) \le b(d(x, y))$ for all $i$, then the family is uniformly equicontinuous (`Metric.uniformEquicontinuous_of_continuity_modulus`), and the local form is `Metric.equicontinuousAt_of_continuity_modulus`. The most frequent case is a common Lipschitz constant: `LipschitzWith.uniformEquicontinuous` and `LipschitzOnWith.uniformEquicontinuousOn`.

#### Common errors

1. `ContractingWith.fixedPoint` needs the instances `Nonempty α` and `CompleteSpace α`. In an extended metric space use `ContractingWith.efixedPoint`, which needs a point $x$ and a proof of `edist x (f x) ≠ ⊤`.
2. `IsUltrametricDist` is a mixin and not a separate metric class. A statement about an ultrametric space has both `[PseudoMetricSpace X]` and `[IsUltrametricDist X]` as hypotheses.
3. The metric on `UniformOnFun α β 𝔖` exists only for finite $\mathfrak{S}$. For the topology of compact convergence, with infinitely many compact sets, there is no instance of this metric.

### Exercises

1. (A) Show that $x \mapsto x/2 + 1$ on $\mathbb{R}$ satisfies `ContractingWith (1/2) f`, and compute its fixed point with `ContractingWith.fixedPoint_unique`.
2. (A) In an ultrametric space, show that $d(x, z) = d(y, z)$ whenever $d(x, y) < d(y, z)$, with `IsUltrametricDist.dist_eq_max_of_dist_ne_dist`.
3. (B) Let $f$ be a map on a complete metric space such that $f^n$ contracts for some $n \ge 1$. Show that $f$ has a unique fixed point, with `ContractingWith.isFixedPt_fixedPoint_iterate`.
4. (B) Show that the snowflake of $[0, 1]$ with $\alpha = 1/2$ admits no injective Lipschitz map to $\mathbb{R}$ whose inverse is Lipschitz. Use the lengths of the images of the intervals $[k/n, (k+1)/n]$.
5. (B) Show that a sequence $f_n$ in `UniformFun α β` converges to $f$ if and only if $\sup_x \operatorname{edist}(f_n(x), f(x)) \to 0$, with `UniformFun.edist_def`.
6. (C) Let $X$ be a compact ultrametric space and let $r > 0$. Prove that the open balls of radius $r$ form a finite partition of $X$ into clopen sets. Deduce that $X$ has a countable basis of clopen sets.

### Reference

<?reference?>
