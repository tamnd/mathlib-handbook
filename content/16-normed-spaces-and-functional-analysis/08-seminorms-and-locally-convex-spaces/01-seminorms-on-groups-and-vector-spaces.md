---
title: Seminorms on groups and vector spaces
kind: api
modules:
  - Mathlib.Analysis.Normed.Group.Seminorm
  - Mathlib.Analysis.Normed.Module.Seminorm.Basic
  - Mathlib.Analysis.Normed.Module.Seminorm.Norm
  - Mathlib.Analysis.Seminorm
explains:
  E2: [AddGroupSeminorm, GroupSeminorm, NonarchAddGroupSeminorm, AddGroupNorm, Seminorm, Seminorm.ofSMulLE, Seminorm.ball_finset_sup_eq_iInter, Seminorm.continuous_iff, normSeminorm, rescale_to_shell]
  E1: auto
families: []
requires: [V05, V07, V13, V16.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Seminorms on groups and vector spaces

### Overview

A seminorm on a vector space $E$ over a normed field $\mathbb{K}$ is a function $p : E \to \mathbb{R}$ with $p(x + y) \le p(x) + p(y)$ and $p(c x) = |c| \, p(x)$. It is a norm without the condition that $p(x) = 0$ implies $x = 0$. Many spaces of analysis have no useful norm but have a family of seminorms. The space of continuous functions on $\mathbb{R}$ has the seminorms $p_n(f) = \sup_{|t| \le n} |f(t)|$, and the space of smooth functions has seminorms for each derivative. The topology of such a space is the coarsest one that makes all the seminorms continuous. These are the locally convex spaces of this chapter.

This section gives the bundled seminorms of Mathlib and their algebra. A seminorm on a group needs no scalars, so Mathlib defines it first for groups and then adds the condition on scalars. The seminorms on a vector space form a lattice, they have balls, and a seminorm is continuous if and only if one of its balls is a neighborhood of $0$.

### The library around it

The module `Mathlib.Analysis.Normed.Group.Seminorm` has six structures. An `AddGroupSeminorm G` on an additive group is a function to $\mathbb{R}$ with $f(0) = 0$, $f(x + y) \le f(x) + f(y)$ and $f(-x) = f(x)$. A `GroupSeminorm G` is the multiplicative form, with $f(1) = 0$ and $f(x y) \le f(x) + f(y)$. A `NonarchAddGroupSeminorm G` satisfies the stronger inequality $f(x + y) \le \max(f(x), f(y))$, the condition of chapter 10. The structures `AddGroupNorm G`, `GroupNorm G` and `NonarchAddGroupNorm G` add the condition that only $0$ has norm $0$. Each structure has a class for maps of its kind, such as `AddGroupSeminormClass`, so that general lemmas such as `map_sub_le_add` and `abs_sub_map_le_sub` apply to all of them. The classes themselves are in the algebra of ordered groups, in `Mathlib.Algebra.Order.Hom.GroupNorm`.

The seminorms on a group form a partial order by pointwise comparison. The sum of two seminorms and the maximum of two seminorms are seminorms, so `AddGroupSeminorm.instAddCommMonoid` and `AddGroupSeminorm.semilatticeSup` give the algebra. The composition `AddGroupSeminorm.comp p f` with a group homomorphism $f$ is a seminorm. A group norm turns a group into a normed group with `AddGroupNorm.toNormedAddGroup`, and a group seminorm gives a seminormed group with `AddGroupSeminorm.toSeminormedAddGroup`. These two constructions are the usual way to build a norm structure from a function.

The structure `Seminorm 𝕜 E` extends `AddGroupSeminorm E` with a field that states $p(c \cdot x) = \|c\| \, p(x)$. The class `SeminormClass` covers all bundled seminorms. To build a seminorm, `Seminorm.of` takes a function with the triangle inequality and the equality for scalars. Over a normed field, `Seminorm.ofSMulLE` needs only the inequality $p(c \cdot x) \le \|c\| \, p(x)$, since the inverse scalar gives the other direction. The norm of a normed space is the seminorm `normSeminorm 𝕜 E`. The lemma `Seminorm.convexOn` states that each seminorm is convex, and `Seminorm.restrictScalars` views a seminorm over $\mathbb{C}$ as a seminorm over $\mathbb{R}$.

The seminorms on a vector space form a lattice, by `Seminorm.instLattice`. The order is pointwise, by `Seminorm.le_def`. The maximum is pointwise, by `Seminorm.sup_apply`. The minimum is not pointwise: `Seminorm.inf_apply` states that $(p \sqcap q)(x) = \inf_u \, (p(u) + q(x - u))$, the infimal convolution. A family of seminorms that is bounded at each point has a supremum, and `Seminorm.bddAbove_range_iff` gives the condition. The bottom element is the zero seminorm, by `Seminorm.instOrderBot`. For a finite set $s$ of indices, `Seminorm.finset_sup_apply` computes the supremum of a finite family pointwise. Families of seminorms reduce to single seminorms by finite suprema in this way, and section 2 uses this often.

Each seminorm has open and closed balls, `Seminorm.ball p x r` and `Seminorm.closedBall p x r`. The lemma `Seminorm.ball_zero_eq` states that the ball at $0$ is the set where $p < r$. For the norm, `ball_normSeminorm` states that the balls are the balls of the metric. The ball of a maximum is the intersection of the balls, by `Seminorm.ball_sup`, and `Seminorm.ball_finset_sup_eq_iInter` gives the form for a finite family. A ball at $0$ is convex, balanced and absorbent, by `Seminorm.convex_ball`, `Seminorm.balanced_ball_zero` and `Seminorm.absorbent_ball_zero`. Section 2 shows that the open convex balanced sets that absorb each point give exactly the balls of continuous seminorms, through the gauge.

A seminorm pulls back along a linear map. For a linear map $f : E \to F$ and a seminorm $p$ on $F$, the seminorm `Seminorm.comp p f` is $x \mapsto p(f x)$, and `Seminorm.ball_comp` states that its balls are the preimages of the balls of $p$. For example, the seminorms $f \mapsto |f(t)|$ on a space of functions are the norm of the scalars composed with the evaluation at $t$. Their finite suprema give the topology of pointwise convergence, and section 3 returns to it.

The continuity of a seminorm depends only on a ball. The lemma `Seminorm.continuous_iff` states that, for $r > 0$, the seminorm $p$ is continuous if and only if `Seminorm.ball p 0 r` is a neighborhood of $0$. The lemma `Seminorm.continuous_of_le` states that a seminorm below a continuous seminorm is continuous. The lemma `Seminorm.uniformContinuous_of_continuousAt_zero` states that continuity at $0$ gives uniform continuity, because $|p(x) - p(y)| \le p(x - y)$.

The module `Mathlib.Analysis.Normed.Module.Seminorm.Norm` also holds the lemmas of rescaling. Over a field with an element $c$ of norm greater than $1$, `rescale_to_shell` moves each nonzero vector into the shell $\varepsilon / \|c\| \le \|x\| < \varepsilon$ with a scalar, and gives a bound for that scalar. The same idea for seminorms is `Seminorm.bound_of_shell`: a bound $q(x) \le C p(x)$ on the shell gives the bound on the whole space. Chapter 2 uses the same idea for the operator norm. The old module `Mathlib.Analysis.Seminorm` is deprecated. It imports `Mathlib.Analysis.Normed.Module.Seminorm.Basic` and has no declarations, so import the new path.

#### Common errors

1. Expecting $p \sqcap q$ to be the pointwise minimum. The pointwise minimum of two seminorms is not subadditive in general. Use `Seminorm.inf_apply`, which gives the infimal convolution.
2. Using `Seminorm.of` when only the inequality for scalars is easy. Over a normed field, `Seminorm.ofSMulLE` proves the equality from the inequality. Over a seminormed ring that is not a field, the inequality is not enough.
3. Confusing the classes. `Seminorm 𝕜 E` needs scalars. A seminorm on a group without scalars is an `AddGroupSeminorm`, and a seminorm on a ring that also controls products is a ring seminorm of chapter 10.

### Exercises

1. (A) Show that $p(f) = |f(0)|$ is a seminorm on the space of continuous functions on $[0, 1]$, and describe the set where $p = 0$.
2. (A) Use `Seminorm.ball_sup` to describe the ball of radius $1$ at $0$ for $p \sqcup q$ on $\mathbb{R}^2$, where $p(x, y) = |x|$ and $q(x, y) = |y|$.
3. (B) Compute $p \sqcap q$ for the two seminorms of exercise 2 with `Seminorm.inf_apply`, and show that it is the zero seminorm.
4. (B) Prove `Seminorm.ofSMulLE`: apply the inequality to $c^{-1}$ and $c \cdot x$.
5. (B) Show that the kernel $\{x \mid p(x) = 0\}$ of a seminorm is a subspace, and that $p$ induces a norm on the quotient by this subspace.
6. (C) Prove `Seminorm.continuous_iff`. Show first that a ball at $0$ is a neighborhood of $0$ for one radius if and only if it is for all radii, and then use the inequality $|p(x) - p(y)| \le p(x - y)$.

### Reference

<?reference?>
