---
title: Bounded continuous functions
kind: api
modules:
  - Mathlib.Topology.ContinuousMap.Bounded.Basic
  - Mathlib.Topology.ContinuousMap.Bounded.Normed
  - Mathlib.Topology.ContinuousMap.Bounded.Star
  - Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
  - Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
  - Mathlib.Topology.Bornology.BoundedOperation
explains:
  E2: [BoundedContinuousFunction.dist_le, BoundedContinuousFunction.tendsto_iff_tendstoUniformly, BoundedContinuousFunction.instCompleteSpace, BoundedContinuousFunction.arzela_ascoli, BoundedContinuousFunction.arzela_ascoli₂, isBounded_mul]
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

## Bounded continuous functions

### Overview

Section 1 puts the supremum metric on `C(X, Y)` when $X$ is compact. For a space $X$ that is not compact, a continuous function can be unbounded, and the supremum of $d(f(x), g(x))$ can be infinite. The remedy is to keep only the bounded functions. A bounded continuous function from a topological space $X$ to a metric space $Y$ is a continuous map whose range is a bounded set. Mathlib writes the type as `X →ᵇ Y`, the notation for `BoundedContinuousFunction X Y`. It carries the supremum metric, and its topology is the topology of uniform convergence.

This type is the main function space of analysis on a space that is not compact. It is complete when $Y$ is complete. It is a normed space, a normed ring or a C*-algebra when $Y$ is one. The theorem of Arzelà and Ascoli describes its compact sets: a set of functions on a compact space with values in a compact set is relatively compact if and only if it is equicontinuous.

The section uses metric spaces and bounded sets from Chapter 3, compactness from Chapter 5, and equicontinuity from Chapter 7.

### The library around it

#### The type and its metric

The module `Mathlib.Topology.ContinuousMap.Bounded.Basic` defines the structure `BoundedContinuousFunction X Y`. It extends `C(X, Y)` with a bound $C$ such that $d(f(x), f(y)) \le C$ for all $x$ and $y$. The class `BoundedContinuousMapClass` is the class of the bundled maps of this kind, in the pattern of `ContinuousMapClass`. The forgetful map is `BoundedContinuousFunction.toContinuousMap`. The usual constructors are:

- `BoundedContinuousFunction.mkOfBound`, from a continuous map and a bound;
- `BoundedContinuousFunction.mkOfCompact`, from a continuous map on a compact space;
- `BoundedContinuousFunction.mkOfDiscrete`, from a bounded function on a discrete space;
- `BoundedContinuousFunction.ofNormedAddCommGroup`, from a continuous function with $\lVert f(x) \rVert \le C$;
- `BoundedContinuousFunction.const`, a constant map.

The distance is the supremum distance. The library defines it as an infimum of bounds: `BoundedContinuousFunction.dist_eq` says that $d(f, g)$ is the infimum of the numbers $C \ge 0$ with $d(f(x), g(x)) \le C$ for all $x$. The set of such $C$ is not empty (`BoundedContinuousFunction.dist_set_exists`), and the infimum is attained. The two working rules follow:

**Proposition.** For $f, g$ in `X →ᵇ Y`, a point $x$ and a number $C \ge 0$:

1. $d(f(x), g(x)) \le d(f, g)$;
2. $d(f, g) \le C$ if and only if $d(f(x), g(x)) \le C$ for all $x$.

*Proof.* The set of the bounds $C$ is closed in $\mathbb{R}$, because each condition $d(f(x), g(x)) \le C$ is closed in $C$. So the infimum $d(f, g)$ is itself a bound, which is the first claim. For the second claim, if $d(f, g) \le C$, then the first claim gives the bound $C$ at each point. Conversely, if $C$ is a bound, then the infimum is at most $C$. $\square$

These are `BoundedContinuousFunction.dist_coe_le_dist` and `BoundedContinuousFunction.dist_le`. The forms for the norm are `BoundedContinuousFunction.norm_le` and `BoundedContinuousFunction.norm_eq_iSup_norm`, which says $\lVert f \rVert = \sup_x \lVert f(x) \rVert$. The rules for a strict inequality need a compact space, because the supremum of a function on a space that is not compact need not be attained: `BoundedContinuousFunction.dist_lt_iff_of_compact`.

The second claim is a statement about uniform convergence. Thus a family $F_i$ tends to $f$ in `X →ᵇ Y` if and only if $F_i \to f$ uniformly on $X$. This is `BoundedContinuousFunction.tendsto_iff_tendstoUniformly`. Evaluation at a point is $1$-Lipschitz (`BoundedContinuousFunction.lipschitz_eval_const`), and the evaluation $(f, x) \mapsto f(x)$ is jointly continuous with no hypothesis on $X$ (`BoundedContinuousFunction.instContinuousEval`). The uniform convergence makes the joint continuity easier than in the compact-open topology.

#### Completeness

**Theorem.** If $Y$ is complete, then `X →ᵇ Y` is complete.

*Proof.* Let $(f_n)$ be a Cauchy sequence. For each $x$, the rule $d(f_n(x), f_m(x)) \le d(f_n, f_m)$ shows that $(f_n(x))$ is a Cauchy sequence in $Y$. Let $f(x)$ be its limit. For $\varepsilon > 0$, choose $N$ with $d(f_n, f_m) \le \varepsilon$ for $n, m \ge N$. Let $m \to \infty$: then $d(f_n(x), f(x)) \le \varepsilon$ for $n \ge N$ and each $x$. So $f_n \to f$ uniformly. A uniform limit of continuous functions is continuous, and $f$ is bounded since it is within $\varepsilon$ of the bounded function $f_N$. By the second rule of the proposition, $d(f_n, f) \le \varepsilon$ for $n \ge N$. $\square$

This is the instance `BoundedContinuousFunction.instCompleteSpace`. By Section 1, `C(X, Y)` for a compact space $X$ is isometric to `X →ᵇ Y`, so it is complete too.

#### Maps between the spaces

A Lipschitz map $G : Y \to Z$ acts by composition on the left: `BoundedContinuousFunction.comp G` is again Lipschitz with the same constant (`BoundedContinuousFunction.lipschitz_comp`). A continuous map $g : W \to X$ acts on the right: `BoundedContinuousFunction.compContinuous` sends $f$ to $f \circ g$, and the norm does not grow (`BoundedContinuousFunction.norm_compContinuous_le`). A function with values in a set $s$ restricts its codomain by `BoundedContinuousFunction.codRestrict`. For an embedding of $X$ into a discrete space $\delta$, the map `BoundedContinuousFunction.extend` extends a function on $X$ by a given function on the rest of $\delta$, and it is an isometry (`BoundedContinuousFunction.isometry_extend`).

#### Bounded operations

The sum of two bounded functions is bounded when the target is a normed group. The target of `X →ᵇ Y` is only a metric space, so the library states the condition as a class. The module `Mathlib.Topology.Bornology.BoundedOperation` defines the classes `BoundedAdd`, `BoundedSub` and `BoundedMul`. Each says that the operation sends two bounded sets to a bounded set.

**Proposition.** In a normed ring $R$, the product $s t$ of two bounded sets is bounded.

*Proof.* If $\lVert a \rVert \le A$ for $a \in s$ and $\lVert b \rVert \le B$ for $b \in t$, then $\lVert a b \rVert \le \lVert a \rVert \lVert b \rVert \le A B$. $\square$

So each seminormed ring has the class (`instBoundedMul`), and `isBounded_mul` states the conclusion for each instance. A Lipschitz multiplication also gives the class (`instBoundedMulOfLipschitzMul`), and a Lipschitz subtraction gives `BoundedSub` (`boundedSub_of_lipschitzWith_sub`). With these classes, `X →ᵇ R` has a product when $R$ has `BoundedMul` and a continuous multiplication (`BoundedContinuousFunction.instMul`).

#### Normed structure

The module `Mathlib.Topology.ContinuousMap.Bounded.Normed` gives the normed structures. The norm is the distance to zero (`BoundedContinuousFunction.norm_def`). The type `X →ᵇ E` is a normed group when $E$ is (`BoundedContinuousFunction.instNormedAddCommGroup`), a normed space over a normed field (`BoundedContinuousFunction.instNormedSpace`), a normed ring (`BoundedContinuousFunction.instNormedRing`) and a normed algebra (`BoundedContinuousFunction.instNormedAlgebra`). The constants give the ring hom `BoundedContinuousFunction.C`, and the forgetful map to `C(X, γ)` is the algebra hom `BoundedContinuousFunction.toContinuousMapₐ`. Evaluation at a point is the continuous linear map `BoundedContinuousFunction.evalCLM`.

The order is pointwise. When the norm of $E$ is solid, that is $|a| \le |b|$ gives $\lVert a \rVert \le \lVert b \rVert$, the type is a lattice with a solid norm (`BoundedContinuousFunction.instLattice`, `BoundedContinuousFunction.instHasSolidNorm`). A real function splits into its positive and negative parts, as functions to $\mathbb{R}_{\ge 0}$: `BoundedContinuousFunction.nnrealPart` and `BoundedContinuousFunction.self_eq_nnrealPart_sub_nnrealPart_neg`. The indicator function of a clopen set is a bounded continuous function (`BoundedContinuousFunction.indicator`).

The module `Mathlib.Topology.ContinuousMap.Bounded.Star` gives the pointwise star (`BoundedContinuousFunction.star_apply`). When $\beta$ is a C*-ring, so is `X →ᵇ β` (`BoundedContinuousFunction.instCStarRing`). The C*-identity $\lVert f^* f \rVert = \lVert f \rVert^2$ holds at each point, and a supremum of squares is the square of the supremum.

#### Compact support

The module `Mathlib.Topology.ContinuousMap.BoundedCompactlySupported` defines the two-sided ideal `compactlySupported X γ` of the bounded continuous functions with compact support, with the notation `C_cb(X, γ)`. Membership is `mem_compactlySupported`. A continuous function with compact support is bounded, so it gives an element by `ofCompactSupport`. On a compact space the ideal is everything (`compactlySupported_eq_top_of_isCompact`). Section 4 studies the same functions as a type of their own.

#### The theorem of Arzelà and Ascoli

A family $A$ of functions $X \to Y$ is equicontinuous if for each $x$ and $\varepsilon > 0$ there is a neighbourhood $U$ of $x$ with $d(f(y), f(x)) < \varepsilon$ for all $y \in U$ and all $f \in A$. The predicate is `Equicontinuous` of Chapter 7.

**Theorem (Arzelà-Ascoli).** Let $X$ be compact and $s \subseteq Y$ compact. Let $A$ be an equicontinuous set of `X →ᵇ Y` whose functions take their values in $s$. Then the closure of $A$ is compact.

This is `BoundedContinuousFunction.arzela_ascoli`, in `Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli`. The form `BoundedContinuousFunction.arzela_ascoli₂` states the compactness of $A$ itself for a closed set $A$.

*Proof sketch.* The closure of $A$ is complete, because the values stay in the complete set $s$. So it suffices to show that $A$ is totally bounded. Fix $\varepsilon > 0$. By equicontinuity, each point $x$ has an open neighbourhood $U_x$ on which each $f \in A$ varies by less than $\varepsilon$. By compactness of $X$, finitely many sets $U_{x_1}, \dots, U_{x_n}$ cover $X$. By compactness of $s$, finitely many balls $B_1, \dots, B_m$ of radius $\varepsilon$ cover $s$. To each $f \in A$ attach the tuple of the indices $j_i$ with $f(x_i) \in B_{j_i}$. There are at most $m^n$ tuples. Two functions $f, g$ with the same tuple satisfy $d(f(y), g(y)) < 4\varepsilon$ at each point $y$: choose $i$ with $y \in U_{x_i}$, and compare $f(y)$, $f(x_i)$, $g(x_i)$ and $g(y)$. So $A$ is covered by at most $m^n$ sets of diameter at most $4 \varepsilon$. $\square$

#### Common errors

1. Using `X →ᵇ Y` for a target that is only a topological space. The type needs a metric space $Y$, because the bound is a bound on distances.
2. Expecting a product on `X →ᵇ R` for each metric ring $R$. The instance needs the class `BoundedMul R`. A normed ring has it, but a general metric ring may not.
3. Stating a strict bound $d(f, g) < C$ from strict bounds at each point. On a space that is not compact the supremum need not be attained, so the rule asks for a compact space.

### Exercises

1. (A) Show that the function $x \mapsto \sin x$ is in `ℝ →ᵇ ℝ` and that $x \mapsto x$ is not.
2. (A) Show that `BoundedContinuousFunction.compContinuous g` is linear and does not increase the norm.
3. (B) Show that the functions $f_n(x) = x^n$ on $[0, 1]$ form a set that is bounded and not equicontinuous, and that the set is not relatively compact in `C([0, 1], ℝ)`.
4. (B) Prove that the uniform limit of a sequence of continuous functions is continuous. Write the $\varepsilon / 3$ argument.
5. (B) Let $X$ be a discrete space. Show that `X →ᵇ ℝ` is the space $\ell^\infty(X)$ of bounded functions, and that it is not separable when $X$ is infinite.
6. (C) Prove the converse of the theorem of Arzelà and Ascoli: a compact set of `X →ᵇ Y`, for a compact space $X$, is equicontinuous.

### Reference

<?reference?>
