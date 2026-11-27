---
title: Normed groups
kind: theory
modules:
  - Mathlib.Analysis.Normed.Group.Defs
  - Mathlib.Analysis.Normed.Group.Basic
  - Mathlib.Analysis.Normed.Group.Continuity
  - Mathlib.Analysis.Normed.Group.Constructions
explains:
  E3: [SeminormedAddCommGroup, NormedAddCommGroup, norm_add_le, dist_eq_norm, abs_norm_sub_norm_le]
  E2: [Norm, norm_nonneg, norm_neg, norm_sub_rev, norm_eq_zero, norm_sum_le, continuous_norm, tendsto_iff_norm_sub_tendsto_zero, pi_norm_le_iff_of_nonneg, Prod.norm_def, NormedAddCommGroup.ofSeparation]
  E1: auto
families: []
requires: [V02, V07, V13]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Normed groups

### Overview

A norm measures the size of an element of an abelian group: the absolute value of a real number, the modulus of a complex number, the length of a vector in the plane. The norm of a difference $\|x - y\|$ is then a distance, and all of the metric topology of Volume 13 applies. This section defines seminorms and norms on an abelian group, proves the triangle inequality in its reverse form, proves that the norm and the group operations are continuous, and builds the norm of a finite product. It then explains how Mathlib sets up the classes `SeminormedAddCommGroup` and `NormedAddCommGroup`. The main point of the Mathlib design is that a normed group already is a metric space, with the metric as data and an axiom that ties it to the norm.

### Definitions

**Definition (Seminorm and norm on a group).** Let $G$ be an abelian group, written additively. A *seminorm* on $G$ is a function $\|\cdot\| : G \to \mathbb{R}$ with

1. $\|0\| = 0$;
2. $\|{-x}\| = \|x\|$ for all $x$;
3. $\|x + y\| \le \|x\| + \|y\|$ for all $x, y$ (the triangle inequality).

A seminorm is a *norm* if also $\|x\| = 0$ implies $x = 0$. A *seminormed group* is an abelian group with a seminorm, and a *normed group* is one with a norm.

A seminorm takes only values $\ge 0$. Indeed $0 = \|0\| = \|x + (-x)\| \le \|x\| + \|{-x}\| = 2\|x\|$. So nonnegativity is not an axiom. The axiom $\|{-x}\| = \|x\|$ is needed: on $\mathbb{Z}$ the function $f(n) = n$ for $n \ge 0$ and $f(n) = 2|n|$ for $n < 0$ satisfies the triangle inequality and $f(0) = 0$, but not the symmetry.

**Definition (The metric of a seminorm).** On a seminormed group put $d(x, y) = \|x - y\|$. This is a pseudometric: $d(x, x) = 0$, $d(x, y) = \|{-(y - x)}\| = d(y, x)$, and
$$d(x, z) = \|(x - y) + (y - z)\| \le d(x, y) + d(y, z).$$
It is a metric if and only if the seminorm is a norm, because $d(x, y) = 0$ means $\|x - y\| = 0$. The metric is translation invariant: $d(x + a, y + a) = d(x, y)$. Each notion of Volume 13 now applies: open balls $B(x, r) = \{y : \|y - x\| < r\}$, convergence, Cauchy sequences, completeness.

::: mathlib
`SeminormedAddCommGroup` · `Mathlib.Analysis.Normed.Group.Defs`

The class extends `Norm E`, `AddCommGroup E` and `PseudoMetricSpace E`, and has one more field, `dist_eq : ∀ x y, dist x y = ‖-x + y‖`. So the distance is part of the data, and the axiom says that it agrees with the norm. The default value of the field `dist` is `fun x y => ‖-x + y‖`, so a user who gives only the norm gets this distance. The triangle inequality of the norm is not a field: it follows from the triangle inequality of the pseudometric through `dist_eq`. The form `‖-x + y‖` in place of `‖x - y‖` comes from the multiplicative version `SeminormedCommGroup`, of which this class is the additive translation.

<?decl SeminormedAddCommGroup?>
:::

::: mathlib
`NormedAddCommGroup` · `Mathlib.Analysis.Normed.Group.Defs`

The same class with `MetricSpace E` in place of `PseudoMetricSpace E`. The separation $\|x\| = 0 \Rightarrow x = 0$ then follows from the separation of the metric. The constructor `NormedAddCommGroup.ofSeparation` builds a normed group from a seminormed group and a proof of the separation. There are also the non-commutative classes `SeminormedAddGroup` and `NormedAddGroup`, used for lemmas that do not need commutativity.

<?decl NormedAddCommGroup?>
:::

Why is the metric a field and not a definition? A type such as $\mathbb{R}$ has its metric before it has a norm. If the normed group structure computed a new metric from the norm, $\mathbb{R}$ would carry two metric structures that are equal as functions but not equal by definition, and two topologies, two uniform structures and two notions of Cauchy sequence. Lean would then fail to see that a lemma about the topology of $\mathbb{R}$ applies to the topology of the normed group $\mathbb{R}$. With the metric as a field, the instance for $\mathbb{R}$ reuses the metric that exists, and proves `dist_eq` once. This pattern is called *forgetful inheritance*, and Mathlib uses it in each structure that carries a topology: the uniform structure of a metric space and the topology of a uniform space are fields in the same way (Volume 13, Chapter 7).

::: mathlib
`Norm` · `Mathlib.Analysis.Normed.Group.Defs`

The class `Norm E` only gives the notation `‖x‖` for a function `E → ℝ`, with no axiom. The notation `‖x‖₊` is the norm as a nonnegative real number, of type `ℝ≥0`, from the class `NNNorm`. It is useful for sums and suprema, where the order of `ℝ≥0` is a complete lattice up to the top element.

<?decl Norm?>
:::

### Theorems and proofs

**Theorem (Basic properties of a seminorm).** In a seminormed group:

1. $\|x\| \ge 0$ and $\|x - y\| = \|y - x\|$;
2. $\|x_1 + \dots + x_n\| \le \|x_1\| + \dots + \|x_n\|$;
3. $\bigl|\|x\| - \|y\|\bigr| \le \|x - y\|$ (the reverse triangle inequality).

*Proof.* Part 1 is in the remarks after the definition and in the computation of $d(y, x)$. Part 2 follows from the triangle inequality by induction on $n$: $\|x_1 + \dots + x_{n+1}\| \le \|x_1 + \dots + x_n\| + \|x_{n+1}\|$. For part 3, write $x = (x - y) + y$. The triangle inequality gives $\|x\| \le \|x - y\| + \|y\|$, so $\|x\| - \|y\| \le \|x - y\|$. Exchange $x$ and $y$ and use part 1: $\|y\| - \|x\| \le \|y - x\| = \|x - y\|$. The two inequalities together say $\bigl|\|x\| - \|y\|\bigr| \le \|x - y\|$. $\square$

::: mathlib
`norm_add_le` · `Mathlib.Analysis.Normed.Group.Basic`

`‖a + b‖ ≤ ‖a‖ + ‖b‖` in a `SeminormedAddGroup`. The finite form is `norm_sum_le` for a `Finset` sum, `‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖`. The symmetry is `norm_neg` and `norm_sub_rev`, the separation is `norm_eq_zero`, which needs `NormedAddGroup`.

<?decl norm_add_le?>
:::

::: mathlib
`abs_norm_sub_norm_le` · `Mathlib.Analysis.Normed.Group.Basic`

The reverse triangle inequality `|‖a‖ - ‖b‖| ≤ ‖a - b‖`. The one-sided form is `norm_sub_norm_le`. The Lipschitz form is `lipschitzWith_one_norm` in `Mathlib.Analysis.Normed.Group.Uniform`.

<?decl abs_norm_sub_norm_le?>
:::

::: mathlib
`dist_eq_norm` · `Mathlib.Analysis.Normed.Group.Basic`

`dist a b = ‖a - b‖`. This is the lemma to rewrite with when a goal mixes the metric and the norm. The special case `dist_zero_right` gives `dist a 0 = ‖a‖`, and `mem_ball_iff_norm` gives `b ∈ ball a r ↔ ‖b - a‖ < r`.

<?decl dist_eq_norm?>
:::

**Theorem (Continuity).** In a seminormed group $G$:

1. the norm $G \to \mathbb{R}$ is $1$-Lipschitz, hence uniformly continuous;
2. addition $G \times G \to G$ and negation $G \to G$ are continuous;
3. $x_n \to x$ if and only if $\|x_n - x\| \to 0$.

*Proof.* Part 1 is the reverse triangle inequality: $\bigl|\|x\| - \|y\|\bigr| \le d(x, y)$. For part 2, let $(x, y)$ be given and $\varepsilon > 0$. If $\|x' - x\| < \varepsilon/2$ and $\|y' - y\| < \varepsilon/2$, then
$$\|(x' + y') - (x + y)\| \le \|x' - x\| + \|y' - y\| < \varepsilon.$$
With the metric $\max(d(x, x'), d(y, y'))$ on the product (Volume 13, Chapter 3), this is continuity at $(x, y)$. Negation is an isometry, since $\|{-x'} - (-x)\| = \|x - x'\| = \|x' - x\|$. Part 3 is the definition of convergence in the metric $d$, since $d(x_n, x) = \|x_n - x\|$. $\square$

So a seminormed group is a topological group whose topology comes from a translation invariant pseudometric. Part 3 reduces each limit in $G$ to a limit of real numbers, and it is the form of convergence that most proofs use.

::: mathlib
`continuous_norm` · `Mathlib.Analysis.Normed.Group.Continuity`

`Continuous fun a ↦ ‖a‖`. The composed form `Continuous.norm` gives continuity of `fun x ↦ ‖f x‖` from continuity of `f`, and it is tagged for the tactics `continuity` and `fun_prop`. The instance that a seminormed group is a topological additive group is found by instance search, so the general lemmas `continuous_add` and `Continuous.add` of Volume 14 apply.

<?decl continuous_norm?>
:::

::: mathlib
`tendsto_iff_norm_sub_tendsto_zero` · `Mathlib.Analysis.Normed.Group.Continuity`

`Tendsto f a (𝓝 b) ↔ Tendsto (fun e ↦ ‖f e - b‖) a (𝓝 0)` for any filter `a`. One lemma serves for sequences, for limits at a point and for limits at infinity, as in Volume 13, Chapter 2.

<?decl tendsto_iff_norm_sub_tendsto_zero?>
:::

**Definition (The norm of a finite product).** Let $G_1, \dots, G_n$ be seminormed groups. On the product $G_1 \times \dots \times G_n$ put
$$\|(x_1, \dots, x_n)\| = \max_i \|x_i\|.$$

**Theorem (Product norm).** This is a seminorm, and a norm if each $\|\cdot\|_{G_i}$ is a norm. Its metric is the maximum metric of Volume 13, so its topology is the product topology.

*Proof.* The zero element has all components $0$, so its norm is $0$. Negation does not change any $\|x_i\|$. For the triangle inequality, for each $i$,
$$\|x_i + y_i\| \le \|x_i\| + \|y_i\| \le \max_j \|x_j\| + \max_j \|y_j\|,$$
and the maximum over $i$ of the left side is then at most the right side. If $\max_i \|x_i\| = 0$, then each $\|x_i\| = 0$, and each $x_i = 0$ when the $G_i$ are normed. The metric is $\max_i \|x_i - y_i\| = \max_i d_i(x_i, y_i)$, the maximum metric, whose topology is the product topology by Volume 13, Chapter 3. $\square$

The maximum is a choice. The sum $\sum_i \|x_i\|$ is also a norm and gives the same topology, since $\max_i \|x_i\| \le \sum_i \|x_i\| \le n \max_i \|x_i\|$. Mathlib uses the maximum because it agrees with the product metric of Volume 13, so the product of normed groups has one topology, one uniform structure and one metric, as forgetful inheritance demands. A different norm on a product needs a different type, `WithLp p (E × F)` or `PiLp p E` of Section 2.

::: mathlib
`pi_norm_le_iff_of_nonneg` · `Mathlib.Analysis.Normed.Group.Constructions`

For a finite family, `0 ≤ r → (‖x‖ ≤ r ↔ ∀ i, ‖x i‖ ≤ r)`. This is how to use the maximum norm of a function `x : (i : ι) → G i` with `[Fintype ι]`. The definition itself is `Pi.norm_def`, a supremum over `Finset.univ` of the `‖x i‖₊`. The single coordinate bound is `norm_le_pi_norm`.

<?decl pi_norm_le_iff_of_nonneg?>
:::

::: mathlib
`Prod.norm_def` · `Mathlib.Analysis.Normed.Group.Constructions`

`‖x‖ = max ‖x.1‖ ‖x.2‖` for `x : E × F`. The instance `Prod.normedAddCommGroup` makes `E × F` a normed group with this norm.

<?decl Prod.norm_def?>
:::

### Examples

**Example (The real and the complex numbers).** On $\mathbb{R}$ the absolute value is a norm, and on $\mathbb{C}$ the modulus $|a + bi| = \sqrt{a^2 + b^2}$ is a norm. The triangle inequality for $\mathbb{C}$ follows from $|z + w|^2 = |z|^2 + 2\operatorname{Re}(z\bar w) + |w|^2 \le (|z| + |w|)^2$, since $\operatorname{Re}(z \bar w) \le |z\bar w| = |z||w|$. In Mathlib the norm of `x : ℝ` is `|x|` by `Real.norm_eq_abs`, and the norm of a complex number is given by `Complex.norm_def` in `Mathlib.Analysis.Complex.Norm`.

**Example (The maximum norm on $\mathbb{R}^3$).** For $x = (3, -4, 1)$ and $y = (1, 1, 1)$ the maximum norm gives $\|x\| = 4$, $\|y\| = 1$ and $\|x + y\| = \|(4, -3, 2)\| = 4 \le 5$. The distance is $d(x, y) = \|(2, -5, 0)\| = 5$. The open ball $B(0, 1)$ is the open cube $(-1, 1)^3$, not the round ball. In Mathlib this is the norm of `Fin 3 → ℝ`, and the round norm needs the type `EuclideanSpace ℝ (Fin 3)` of Section 2.

**Example (A seminorm that is not a norm).** On $\mathbb{R}^2$ put $p(x_1, x_2) = |x_1|$. The three axioms hold, but $p(0, 1) = 0$. The pseudometric does not separate $(0, 0)$ and $(0, 1)$, and the topology is not Hausdorff. The set $N = \{x : p(x) = 0\}$ is the subgroup $\{0\} \times \mathbb{R}$, and $p$ becomes a norm on the quotient $\mathbb{R}^2 / N \cong \mathbb{R}$. Chapter 4 studies such quotients.

**Example (The sup norm on bounded functions).** Let $S$ be a set and $B(S)$ the group of bounded functions $f : S \to \mathbb{R}$. Then $\|f\|_\infty = \sup_{s \in S} |f(s)|$ is a norm. The triangle inequality: for each $s$, $|f(s) + g(s)| \le |f(s)| + |g(s)| \le \|f\|_\infty + \|g\|_\infty$, and the supremum over $s$ keeps the bound. Convergence in this norm is uniform convergence on $S$. For $S$ infinite this is the first normed group of infinite dimension. Mathlib has it as the type `BoundedContinuousFunction` for a topological space $S$, written `S →ᵇ ℝ`, in `Mathlib.Topology.ContinuousMap.Bounded.Basic`.

**Counterexample (Symmetry is an axiom).** The function $f$ on $\mathbb{Z}$ from the definitions, $f(n) = n$ for $n \ge 0$ and $f(n) = 2|n|$ for $n < 0$, satisfies $f(0) = 0$ and the triangle inequality, as a check of the four sign cases shows. Its "distance" $f(x - y)$ is not symmetric: $f(1 - 0) = 1$ and $f(0 - 1) = 2$. So the triangle inequality and $f(0) = 0$ alone do not give a pseudometric.

### The library around it

The files of `Mathlib.Analysis.Normed.Group` give the API of normed groups. `Defs` has the classes, `Basic` the inequalities, `Continuity` the limits, `Uniform` the uniform structure and the Lipschitz lemmas, and `Constructions` the products, the functions on a finite type and the subgroups. Most lemmas exist in a multiplicative form, for a normed multiplicative group, and the additive form is generated from it: `norm_mul_le'` and `norm_add_le`, `norm_inv'` and `norm_neg`. A reader who sees a name with a prime and a multiplication sign is looking at the multiplicative form. The lemmas about `‖·‖₊` have the same names with `nnNorm` in place of `norm`: `nnNorm_add_le`, `nnNorm_neg`. Mathlib also has the structures `AddGroupSeminorm` and `AddGroupNorm` in `Mathlib.Analysis.Normed.Group.Seminorm`, for a seminorm that is not the canonical one of the type.

Common errors of a learner:

- Writing a normed group as a group with a norm and then defining a metric from it. In Mathlib the metric is already there, and a second metric is a second structure.
- Expecting `‖x‖ = 0 → x = 0` in a `SeminormedAddCommGroup`.
- Using the Euclidean norm on `Fin n → ℝ`. Its norm is the maximum norm.
- Forgetting that the reverse triangle inequality has an absolute value on the left.

### Exercises

1. (A) Show that $\|x\| - \|y\| \le \|x + y\|$ in a seminormed group.
2. (A) Compute $\|x\|$, $\|y\|$ and $d(x, y)$ for $x = (1, -2, 5)$ and $y = (-3, 0, 2)$ with the maximum norm on $\mathbb{R}^3$.
3. (A) Show that in a normed group the closed ball $\{y : \|y - x\| \le r\}$ is closed. Hint: the norm is continuous.
4. (B) Let $p$ be a seminorm on $G$. Show that $N = \{x : p(x) = 0\}$ is a subgroup and that $p(x + n) = p(x)$ for $n \in N$. Conclude that $p$ gives a norm on $G/N$.
5. (B) Show that $x_n \to x$ implies $\|x_n\| \to \|x\|$, and give an example in $\mathbb{R}$ where $\|x_n\|$ converges but $x_n$ does not.
6. (B) Show that $f \mapsto \sup_{t \in [0,1]} |f(t)| + |f(0)|$ is a norm on the bounded functions on $[0, 1]$, with the same convergent sequences as $\|\cdot\|_\infty$.
7. (C) Let $G$ be an abelian group with a translation invariant metric $d$, that is $d(x + a, y + a) = d(x, y)$. Show that $\|x\| = d(x, 0)$ is a norm whose metric is $d$. Hint: $d(-x, 0) = d(0, x)$ by translation by $x$.

### Notes and history

The axioms of a norm on a vector space appear in Banach's thesis of 1920, published in 1922, and in his book *Théorie des opérations linéaires* of 1932. The general setting of a seminormed group lets Mathlib treat the integers, the $p$-adic numbers and the vector spaces in one frame. The files `Mathlib.Analysis.Normed.Group.Defs`, `Basic` and `Constructions` have the authors Patrick Massot, Johannes Hölzl and Yaël Dillies.

### Reference

<?reference?>
