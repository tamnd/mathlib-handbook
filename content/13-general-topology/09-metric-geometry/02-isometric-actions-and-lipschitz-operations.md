---
title: Isometric actions and Lipschitz operations
kind: api
modules:
  - Mathlib.Topology.MetricSpace.IsometricSMul
  - Mathlib.Topology.MetricSpace.Algebra
explains:
  E2: [dist_mul_left, dist_inv_inv, Metric.smul_ball, IsometryEquiv.constSMul, LipschitzMul.continuousMul, IsBoundedSMul.continuousSMul, dist_pair_smul]
  E1: auto
families: []
requires: [V04, V13.C01, V13.C03, V13.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Isometric actions and Lipschitz operations

### Overview

Many metric spaces carry an algebraic structure. In a normed group the distance satisfies $d(a + b, a + c) = d(b, c)$, so each translation is an isometry. On $\mathbb{R}_{\ge 0}$ addition is Lipschitz, and multiplication by a number $c$ multiplies distances by $c$. This section describes two modules that state such compatibilities as classes, so that a lemma proved once applies to each structure with the class.

The module `Mathlib.Topology.MetricSpace.IsometricSMul` defines the class `IsIsometricSMul M X`: each map $x \mapsto c \cdot x$ is an isometry. The additive form is `IsIsometricVAdd`. The module `Mathlib.Topology.MetricSpace.Algebra` defines three weaker classes: `LipschitzAdd`, `LipschitzMul` and `IsBoundedSMul`. The section uses the isometries of Section 1 and the Lipschitz maps of Chapter 3.

### The library around it

#### The class of isometric actions

Let $M$ act on a pseudo extended metric space $X$. The class `IsIsometricSMul M X` has one field, `IsIsometricSMul.isometry_smul`: for each $c \in M$ the map $x \mapsto c \cdot x$ is an isometry. The constructor `IsIsometricSMul.mk` takes this family of isometries. The class needs no algebraic axiom on $M$, and it is a mixin: it adds a property to a scalar multiplication that already exists.

The case $X = M$ with left multiplication is `IsIsometricSMul M M`. It says $d(a b, a c) = d(b, c)$, the left invariance of the distance. Right multiplication is the action of the opposite monoid $M^{\mathrm{mop}}$, so right invariance is `IsIsometricSMul Mᵐᵒᵖ M`. A group with a distance that is left and right invariant has both instances. A normed commutative group is the main example, and the files on normed groups give its instances. For a commutative monoid one instance gives the other: `IsIsometricSMul.opposite_of_comm`.

The library gives the instances that a proof expects from the constructions. An action on each factor gives an isometric action on a product (`Prod.instIsIsometricSMul`) and on a finite product with the sup distance (`instIsIsometricSMulForall`). Componentwise actions of a family of monoids give `Pi.isIsometricSMul'`. The units of $M$ act by isometries if $M$ does (`Units.isIsometricSMul`). The classes move between `Additive` and `Multiplicative`: `Additive.isIsIsometricVAdd` and `Multiplicative.isIsometricSMul`. An isometric action is continuous in the second variable, so `IsIsometricSMul.to_continuousConstSMul` gives `ContinuousConstSMul M X`.

#### Distances, balls and diameters

The main lemmas say that an action, a multiplication or an inversion keeps distances. The names start with dist and then name the operation. The forms for the extended distance and the nonnegative distance start with edist and nnDist.

| Lean name | Statement | Class needed |
|---|---|---|
| `dist_smul` | $d(c x, c y) = d(x, y)$ | `IsIsometricSMul M X` |
| `dist_mul_left` | $d(a b, a c) = d(b, c)$ | `IsIsometricSMul M M` |
| `dist_mul_right` | $d(a c, b c) = d(a, b)$ | `IsIsometricSMul Mᵐᵒᵖ M` |
| `dist_div_right` | $d(a / c, b / c) = d(a, b)$ | `IsIsometricSMul Mᵐᵒᵖ M` |
| `dist_inv_inv` | $d(a^{-1}, b^{-1}) = d(a, b)$ | both, for a group |
| `dist_div_left` | $d(a / b, a / c) = d(b, c)$ | both, for a group |
| `dist_vadd` | $d(c + x, c + y) = d(x, y)$ | `IsIsometricVAdd M X` |
| `dist_add_left` | $d(a + b, a + c) = d(b, c)$ | `IsIsometricVAdd M M` |
| `dist_neg_neg` | $d(-a, -b) = d(a, b)$ | both, for an additive group |

The lemma `dist_inv_inv` has a short proof. Multiply on the left by $a$ and on the right by $b$: $d(a^{-1}, b^{-1}) = d(a a^{-1} b, a b^{-1} b) = d(b, a) = d(a, b)$. The first step uses left invariance, the second right invariance, and the last the symmetry of the distance.

The same isometries act on sets. For a group action, `Metric.smul_ball` states $c \cdot B(x, r) = B(c \cdot x, r)$, and `Metric.smul_closedBall` and `Metric.smul_sphere` give the closed balls and spheres. The preimage forms are `Metric.preimage_smul_ball` and, for the left and right multiplication of a group, `Metric.preimage_mul_left_ball` and `Metric.preimage_mul_right_ball`. The last one states that $\{x : x a \in B(b, r)\} = B(b / a, r)$. The diameter is invariant (`diam_smul` and `ediam_smul`), and a translate of a bounded set is bounded (`Bornology.IsBounded.smul`). The distance to a set is also invariant: `Metric.infEDist_smul` in the module of Section 3.

#### Isometric bijections from an action

For a group action, the map $x \mapsto c \cdot x$ has the inverse $x \mapsto c^{-1} \cdot x$, so it is an isometric bijection. The library names these bijections as follows.

| Lean name | Map |
|---|---|
| `IsometryEquiv.constSMul c` | $x \mapsto c \cdot x$ on $X$ |
| `IsometryEquiv.mulLeft c` | $x \mapsto c x$ on $G$ |
| `IsometryEquiv.mulRight c` | $x \mapsto x c$ on $G$ |
| `IsometryEquiv.divLeft c` | $x \mapsto c / x$ on $G$ |
| `IsometryEquiv.divRight c` | $x \mapsto x / c$ on $G$ |
| `IsometryEquiv.inv G` | $x \mapsto x^{-1}$ on $G$ |
| `IsometryEquiv.constVAdd c`, `IsometryEquiv.addLeft c`, `IsometryEquiv.neg G` | the additive forms |

Each has a lemma for its value and a lemma for its inverse. For example `IsometryEquiv.constSMul_apply` states that the map sends $x$ to $c \cdot x$, and `IsometryEquiv.constSMul_symm` states that its inverse is `IsometryEquiv.constSMul c⁻¹`. The unbundled forms `isometry_mul_left`, `isometry_inv` and `isometry_neg` give the predicate `Isometry` directly.

#### Lipschitz addition and multiplication

The module `Mathlib.Topology.MetricSpace.Algebra` gives classes for monoids in which the operation is Lipschitz, but not an isometry in each variable. The class `LipschitzAdd β` says that there is a constant $C$ such that $(p, q) \mapsto p + q$ is $C$-Lipschitz on $\beta \times \beta$ (`LipschitzAdd.lipschitz_add`). The class `LipschitzMul β` is the multiplicative form. The constants are chosen by `LipschitzAdd.C` and `LipschitzMul.C`, and `lipschitz_with_lipschitz_const_add` states the bound $d(p_1 + p_2, q_1 + q_2) \le C \cdot d(p, q)$. The main consequence is continuity: `LipschitzAdd.continuousAdd` and `LipschitzMul.continuousMul`. A Lipschitz map is continuous, and the operation is a Lipschitz map on the product.

The instances are `Real.hasLipschitzAdd` and `NNReal.hasLipschitzAdd`, together with the transfer to submonoids (`Submonoid.lipschitzMul`), opposites (`MulOpposite.lipschitzMul`) and order duals (`instLipschitzAddOrderDual`). Multiplication on $\mathbb{R}$ is not Lipschitz on $\mathbb{R} \times \mathbb{R}$, because $d(x^2, y^2) = |x + y| \cdot |x - y|$ has no uniform bound. So $\mathbb{R}$ has no `LipschitzMul` instance.

#### Bounded scalar multiplication

The class `IsBoundedSMul α β` describes a scalar multiplication between two pseudometric spaces with zero elements. It has two inequalities, one for each variable.

1. `dist_smul_pair`: $d(x y_1, x y_2) \le d(x, 0) \cdot d(y_1, y_2)$.
2. `dist_pair_smul`: $d(x_1 y, x_2 y) \le d(x_1, x_2) \cdot d(y, 0)$.

In a normed space these are $\|x y_1 - x y_2\| \le \|x\| \|y_1 - y_2\|$ and the same with the roles exchanged. The class is the metric form of the inequality $\|x y\| \le \|x\| \|y\|$. The constructor is `IsBoundedSMul.mk`, and the instances in the module are `Real.isBoundedSMul`, `NNReal.isBoundedSMul`, `Prod.instIsBoundedSMul`, `Pi.instIsBoundedSMul`, the separation quotient (`instIsBoundedSMulSeparationQuotient`) and the opposite action (`IsBoundedSMul.op`).

The main result is `IsBoundedSMul.continuousSMul`: the scalar multiplication is jointly continuous. The proof is the usual estimate for a product. With the triangle inequality and the two fields,
$$d(x y, x_0 y_0) \le d(x y, x y_0) + d(x y_0, x_0 y_0) \le d(x, 0) \, d(y, y_0) + d(x, x_0) \, d(y_0, 0),$$
and the right side tends to $0$ when $x \to x_0$ and $y \to y_0$, since $d(x, 0)$ stays bounded. The same estimate gives uniform continuity on bounded sets (`Bornology.IsBounded.uniformContinuousOn_smul`) and the instance `IsBoundedSMul.toUniformContinuousConstSMul`.

The module ends with locally uniform limits. If $F_n \to f$ and $G_n \to g$ locally uniformly, and $f$ and $g$ are continuous, then $F_n G_n \to f g$ locally uniformly: `TendstoLocallyUniformly.mul₀` and the scalar form `TendstoLocallyUniformly.smul₀`. The forms `TendstoLocallyUniformlyOn.mul₀` work on a subset, and the forms whose names end in of_isBoundedUnder replace continuity by local boundedness of the limits.

#### Common errors

1. Right invariance is the class `IsIsometricSMul Mᵐᵒᵖ M`, not a separate class. A lemma such as `dist_mul_right` fails with a missing instance when only left invariance is known.
2. `LipschitzMul` does not hold for $\mathbb{R}$. A proof about products of real functions uses `IsBoundedSMul` or the normed ring structure, not `LipschitzMul`.
3. The two fields of `IsBoundedSMul` use the distance to $0$, not a norm. The class makes sense for a pseudometric space with a zero element and no norm, such as $\mathbb{R}_{\ge 0}$.

### Exercises

1. (A) Use `dist_mul_left` and `dist_mul_right` to prove $d(a b, a' b') \le d(a, a') + d(b, b')$ in a group with a left and right invariant distance.
2. (A) Show that `IsometryEquiv.mulLeft a` composed with `IsometryEquiv.mulLeft b` is `IsometryEquiv.mulLeft (a * b)`, as functions.
3. (B) Prove that a left invariant distance on a group is right invariant if and only if inversion is an isometry.
4. (B) Show that addition on $\mathbb{R}$ is Lipschitz with constant $2$ for the sup distance on $\mathbb{R} \times \mathbb{R}$, and that no smaller constant works. Deduce an instance of `LipschitzAdd ℝ` and compare it with `Real.hasLipschitzAdd`.
5. (B) Prove from the two fields of `IsBoundedSMul ℝ ℝ` that multiplication on $\mathbb{R}$ is uniformly continuous on each bounded subset of $\mathbb{R} \times \mathbb{R}$.
6. (B) Let $G$ act by isometries on a metric space $X$ and let $x \in X$. Show that the stabilizer of $x$ acts on each sphere centred at $x$.

### Reference

<?reference?>
