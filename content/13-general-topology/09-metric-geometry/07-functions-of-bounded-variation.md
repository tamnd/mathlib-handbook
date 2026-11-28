---
title: Functions of bounded variation
kind: api
modules:
  - Mathlib.Topology.EMetricSpace.BoundedVariation
  - Mathlib.Topology.EMetricSpace.VariationOnFromTo
explains:
  E2: [eVariationOn.Icc_add_Icc, eVariationOn.edist_le, MonotoneOn.eVariationOn_eq, LipschitzOnWith.comp_eVariationOn_le, LipschitzWith.locallyBoundedVariationOn, variationOnFromTo.add, variationOnFromTo.sub_self_monotoneOn, LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn, BoundedVariationOn.countable_not_continuousAt]
  E1: auto
families: []
requires: [V04, V13.C01, V13.C02, V13.C03, V13.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Functions of bounded variation

### Overview

Let $f$ be a function from a linearly ordered set to a metric space. The variation of $f$ on a set $s$ measures the total distance that $f(x)$ travels when $x$ moves through $s$ in increasing order. A function has bounded variation when this distance is finite. Monotone real functions and Lipschitz functions on an interval have bounded variation. A continuous function can fail to have bounded variation: $x \sin(1/x)$ on $[0, 1]$ is an example.

The two modules of this section define the variation and prove its main properties. The variation is additive on adjacent intervals, it does not increase under monotone reparametrization, and it is lower semicontinuous in $f$. For real functions, the signed variation gives the Jordan decomposition: a function of locally bounded variation is a difference of two monotone functions. A function of bounded variation has one-sided limits at each point when the target is complete, and it is continuous outside a countable set.

The section uses the extended metric spaces and the filters of the earlier chapters. Volume 15 uses these results for the differentiability of monotone and Lipschitz functions, and the measure theory volume uses them to build Stieltjes measures.

### The library around it

#### The variation and the two predicates

Let $\alpha$ be a linear order and let $E$ have an extended pseudometric. The variation of $f : \alpha \to E$ on $s \subseteq \alpha$ is

$$\operatorname{Var}(f, s) = \sup \Big\{ \sum_{i < n} \operatorname{edist}(f(u_{i+1}), f(u_i)) \Big\},$$

where the supremum is over $n \in \mathbb{N}$ and the monotone sequences $u : \mathbb{N} \to \alpha$ with all values in $s$. In Lean this is `eVariationOn f s`, a value in $[0, \infty]$. The choice of $[0, \infty]$ is deliberate. It is a complete lattice, so the supremum always exists and no proof of boundedness is necessary. The lemma `eVariationOn.eVariationOn_eq_strictMonoOn` gives the same supremum over strictly monotone sequences.

The two predicates are short definitions on top of the variation.

| Lean name | Statement |
|---|---|
| `BoundedVariationOn f s` | `eVariationOn f s ≠ ∞` |
| `LocallyBoundedVariationOn f s` | for all $a, b \in s$, `BoundedVariationOn f (s ∩ Set.Icc a b)` |
| `BoundedVariationOn.locallyBoundedVariationOn` | bounded variation implies locally bounded variation |
| `BoundedVariationOn.mono` | bounded variation passes to a subset |
| `BoundedVariationOn.of_finite` | a function on a finite set, with values in a metric space, has bounded variation |
| `BoundedVariationOn.of_subsingleton` | a function on a set with at most one point has bounded variation |

The definitions use the class `WeakPseudoEMetricSpace` for the target, so the topology of $E$ is not required to come from its distance. In a usual pseudometric space this class is automatic, and a reader can ignore it.

#### Basic computations

The defining inequality is `eVariationOn.sum_le`: each sum over a monotone sequence in $s$ is at most the variation. Two points give the first estimate.

**Proposition** (`eVariationOn.edist_le`). For $x, y \in s$, $\operatorname{edist}(f(x), f(y)) \le \operatorname{Var}(f, s)$.

*Proof.* Assume $x \le y$. The sequence $u_0 = x$, $u_i = y$ for $i \ge 1$ is monotone with values in $s$. Its sum with $n = 1$ is $\operatorname{edist}(f(y), f(x))$, and this sum is at most the variation. The case $y \le x$ is symmetric.

The real forms are `BoundedVariationOn.dist_le` and, for real $f$, `BoundedVariationOn.sub_le`: they state $\operatorname{dist}(f(x), f(y)) \le \operatorname{Var}(f, s)$ with the variation cast to $\mathbb{R}$ by `ENNReal.toReal`. The other basic facts are as follows. The variation is monotone in the set (`eVariationOn.mono`). It depends only on the values of $f$ on $s$ (`eVariationOn.congr`). It vanishes on a set with at most one point (`eVariationOn.subsingleton`) and for a function with at most one value on $s$ (`eVariationOn.constant_on`). On a pair it is the distance: `eVariationOn.pair` says $\operatorname{Var}(f, \{a, b\}) = \operatorname{edist}(f(a), f(b))$. Along the points $u_0 \le \dots \le u_n$ of a monotone sequence, `eVariationOn.image_range_of_monotone` gives the sum of the distances of consecutive values.

#### Additivity

The variation is additive on sets that touch at one point. The general form is `eVariationOn.union`: if $x$ is the greatest element of $s$ and the least element of $t$, then $\operatorname{Var}(f, s \cup t) = \operatorname{Var}(f, s) + \operatorname{Var}(f, t)$. Without a common point, only one inequality holds: `eVariationOn.add_le_union` gives $\operatorname{Var}(f, s) + \operatorname{Var}(f, t) \le \operatorname{Var}(f, s \cup t)$ when $s$ is to the left of $t$. The interval form is the one that a user meets most.

**Proposition** (`eVariationOn.Icc_add_Icc`). Let $a \le b \le c$ with $b \in s$. Then
$$\operatorname{Var}(f, s \cap [a, b]) + \operatorname{Var}(f, s \cap [b, c]) = \operatorname{Var}(f, s \cap [a, c]).$$

*Proof sketch.* The inequality $\le$ is `eVariationOn.add_le_union`, because $s \cap [a, b]$ is to the left of $s \cap [b, c]$ and their union is $s \cap [a, c]$. For $\ge$, take a monotone sequence in $s \cap [a, c]$. The lemma `eVariationOn.add_point` inserts the point $b$ into the sequence, and an extra point does not decrease the sum, by the triangle inequality. The new sequence splits at $b$ into a sequence in $s \cap [a, b]$ and a sequence in $s \cap [b, c]$, so its sum is at most the right side.

The finite form `eVariationOn.sum` adds the variations on $s \cap [E_i, E_{i+1}]$ for a monotone sequence $E$. The lemmas `eVariationOn.eVariationOn_on_inter_Iic_eq_Iio_add_edist` and `eVariationOn.eVariationOn_on_inter_Ici_eq_Ioi_add_edist` compare a closed half line with the open one, and the correction is the jump at the end point.

#### Monotone functions, reparametrization and Lipschitz maps

For a monotone real function the variation is the increment.

**Proposition** (`MonotoneOn.eVariationOn_eq`). If $f$ is monotone on $s$ and $a, b \in s$, then $\operatorname{Var}(f, s \cap [a, b]) = \max(f(b) - f(a), 0)$, written `ENNReal.ofReal (f b - f a)`.

*Proof.* For a monotone sequence $u$ in $s \cap [a, b]$ with $a \le b$, the sum $\sum_{i < n} |f(u_{i+1}) - f(u_i)|$ telescopes to $f(u_n) - f(u_0) \le f(b) - f(a)$. The sequence $a, b, b, \dots$ attains the bound. When $b < a$ the set is empty and both sides are $0$.

The consequences are `MonotoneOn.locallyBoundedVariationOn` and `MonotoneOn.boundedVariationOn`: a monotone function has locally bounded variation, and bounded variation when it is bounded. The identity of $\mathbb{R}$ is the basic example: `eVariationOn_id_Icc` gives $\operatorname{Var}(\mathrm{id}, [a, b]) = b - a$ and `BoundedVariationOn.id_Icc` records the finiteness.

A monotone change of variable does not increase the variation. Let $\varphi$ be monotone on $t$ with values in $s$. Then `eVariationOn.comp_le_of_monotoneOn` gives $\operatorname{Var}(f \circ \varphi, t) \le \operatorname{Var}(f, s)$, and `eVariationOn.comp_eq_of_monotoneOn` gives the equality $\operatorname{Var}(f \circ \varphi, t) = \operatorname{Var}(f, \varphi(t))$. The antitone forms are `eVariationOn.comp_le_of_antitoneOn` and `eVariationOn.comp_eq_of_antitoneOn`. The form `eVariationOn.comp_ofDual` passes to the reversed order.

A Lipschitz map multiplies the variation by at most its constant.

**Proposition** (`LipschitzOnWith.comp_eVariationOn_le`). If $f$ is $C$-Lipschitz on $t$ and $g$ maps $s$ into $t$, then $\operatorname{Var}(f \circ g, s) \le C \operatorname{Var}(g, s)$.

*Proof.* For each monotone sequence $u$ in $s$, the distance $\operatorname{edist}(f(g(u_{i+1})), f(g(u_i)))$ is at most $C \operatorname{edist}(g(u_{i+1}), g(u_i))$. Sum over $i$, then take the supremum.

The forms `LipschitzOnWith.comp_boundedVariationOn`, `LipschitzWith.comp_boundedVariationOn` and their locally bounded variants follow. With $g = \mathrm{id}$ on an interval of $\mathbb{R}$, they give the next result.

**Proposition** (`LipschitzWith.locallyBoundedVariationOn`). A Lipschitz function $f : \mathbb{R} \to E$ has locally bounded variation on each set $s$.

*Proof.* On $s \cap [a, b]$, the variation of $f = f \circ \mathrm{id}$ is at most $C \operatorname{Var}(\mathrm{id}, s \cap [a, b]) \le C (b - a)$, which is finite.

The variation is lower semicontinuous in $f$. The lemma `eVariationOn.lowerSemicontinuous` states it for pointwise convergence on $s$, and `eVariationOn.lowerSemicontinuous_uniformOn` for uniform convergence on $s$. So a limit of functions with variation at most $V$ has variation at most $V$.

#### The signed variation and the Jordan decomposition

The signed variation `variationOnFromTo f s a b` is a real number. For $a \le b$ it is the variation on $s \cap [a, b]$, cast to $\mathbb{R}$. For $b < a$ it is the opposite of the variation on $s \cap [b, a]$. The value is useful only when the variation is finite, so most lemmas assume `LocallyBoundedVariationOn f s`. The basic facts are `variationOnFromTo.self` (the value at $a = b$ is $0$), `variationOnFromTo.nonneg_of_le` and `variationOnFromTo.nonpos_of_ge` (the sign), and `variationOnFromTo.abs_le_eVariationOn` (the bound by the total variation).

**Proposition** (`variationOnFromTo.add`). If $f$ has locally bounded variation on $s$ and $a, b, c \in s$, then $V(a, b) + V(b, c) = V(a, c)$, where $V$ is the signed variation.

*Proof sketch.* For $a \le b \le c$ this is `eVariationOn.Icc_add_Icc` cast to $\mathbb{R}$; the cast is additive because both terms are finite. The other orders of $a, b, c$ follow from this case, because the signed variation changes sign when its two points are exchanged.

So $x \mapsto V(a, x)$ is monotone on $s$ (`variationOnFromTo.monotoneOn`), and $x \mapsto V(x, b)$ is antitone (`variationOnFromTo.antitoneOn`). The lemmas `variationOnFromTo.sub_left` and `variationOnFromTo.sub_right` express a difference of two signed variations as a third one. If the signed variation between two points is $0$, the values at the two points have distance $0$ (`variationOnFromTo.edist_zero_of_eq_zero`).

For a real function, the key inequality is `variationOnFromTo.abs_sub_le_sub_of_le`: for $b \le c$, $|f(c) - f(b)| \le V(a, c) - V(a, b)$. It gives the Jordan decomposition.

**Proposition** (`variationOnFromTo.sub_self_monotoneOn`). If $f : \alpha \to \mathbb{R}$ has locally bounded variation on $s$ and $a \in s$, then $x \mapsto V(a, x) - f(x)$ is monotone on $s$.

*Proof.* Let $b \le c$ in $s$. By the inequality above, $f(c) - f(b) \le V(a, c) - V(a, b)$. Rearranged, this is $V(a, b) - f(b) \le V(a, c) - f(c)$.

The same argument with $f(b) - f(c)$ gives `variationOnFromTo.add_self_monotoneOn`: $x \mapsto V(a, x) + f(x)$ is monotone.

**Theorem** (`LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn`). A real function of locally bounded variation on $s$ is the difference $p - q$ of two functions that are monotone on $s$.

*Proof.* If $s$ is empty, take $p = f$ and $q = 0$. Otherwise fix $a \in s$, and take $p(x) = V(a, x)$ and $q(x) = V(a, x) - f(x)$. Then $p$ is monotone by `variationOnFromTo.monotoneOn`, $q$ is monotone by the previous proposition, and $p - q = f$.

The primed form `LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn'` adds that the increments of $p$ and $q$ add up to the signed variation: $p(y) - p(x) + (q(y) - q(x)) = V(x, y)$.

#### Limits and continuity

Let $\alpha$ carry its order topology. A function of bounded variation with values in a complete space has one-sided limits. The lemmas `BoundedVariationOn.exists_tendsto_left` and `BoundedVariationOn.exists_tendsto_right` give a limit of $f$ at $x$ from the left and from the right within $s$, and `BoundedVariationOn.exists_tendsto_atTop` and `BoundedVariationOn.exists_tendsto_atBot` give the limits at the two ends. The proof is a Cauchy argument: by `BoundedVariationOn.tendsto_eVariationOn_Ici_zero`, the variation on $s \cap [y, \infty)$ tends to $0$ as $y \to \infty$, and this variation bounds the distance between any two values on the tail.

With `Function.leftLim` and `Function.rightLim` from the order part of the library, these limits become functions. The lemma `BoundedVariationOn.leftLim` says that the left limit function of a function of bounded variation also has bounded variation, and `BoundedVariationOn.continuousWithinAt_leftLim` says that it is continuous from the left. The jumps of the signed variation are the jumps of $f$: `variationOnFromTo.leftLim_eq` gives

$$\lim_{x \to b^-} V(a, x) = V(a, b) - \operatorname{dist}(f(b), f(b^-)),$$

and `variationOnFromTo.rightLim_eq` gives the right form. The lemma `BoundedVariationOn.continuousAt_variationOnFromTo_iff` says that $x \mapsto V(a, x)$ is continuous at $x$ if and only if $f$ is.

**Theorem** (`BoundedVariationOn.countable_not_continuousAt`). A function $g : \alpha \to M$ of bounded variation on all of $\alpha$ is continuous outside a countable set.

*Proof sketch.* By the previous lemma, $g$ and $x \mapsto V(a, x)$ have the same points of discontinuity. The second function is a monotone real function, and a monotone function on a linear order has only countably many discontinuities: each one has a jump of positive size, and only finitely many jumps exceed $1/n$ since the total is finite.

#### Common errors

1. The variation is a value in `ENNReal`, not in $\mathbb{R}$. To get a real bound, use `BoundedVariationOn.dist_le`, which contains the cast `ENNReal.toReal`. For a function of infinite variation the cast is $0$, so a real statement without the hypothesis `BoundedVariationOn f s` is usually false.
2. `LocallyBoundedVariationOn f s` asks for finite variation on $s \cap [a, b]$ for end points $a, b$ in $s$, not for all $a, b$ in $\alpha$. On $s = \mathbb{Q}$, the end points must be rational.
3. The signed variation `variationOnFromTo f s a b` is defined for all $f$, but its lemmas need locally bounded variation. Without it, the cast of $\infty$ to $\mathbb{R}$ is $0$, and the additivity `variationOnFromTo.add` fails.

### Exercises

1. (A) Show that $f(x) = |x - 1|$ has variation $2$ on $[0, 2]$. Split the interval at $1$ with `eVariationOn.Icc_add_Icc`, and treat each half with `MonotoneOn.eVariationOn_eq`, applied to $f$ or to $x \mapsto 1 - x$.
2. (A) Let $f_n \to f$ pointwise on $s$, and let each $f_n$ have variation at most $V$ on $s$. Show that $f$ has variation at most $V$ on $s$, with `eVariationOn.lowerSemicontinuous`.
3. (B) Prove that $\operatorname{Var}(f + g, s) \le \operatorname{Var}(f, s) + \operatorname{Var}(g, s)$ for real functions $f$ and $g$, from the definition of `eVariationOn` and the triangle inequality.
4. (B) Show that the function $x \sin(1/x)$, extended by $0$ at $0$, does not have bounded variation on $[0, 1]$. Use the points $x_k = 2/((2k+1)\pi)$ and `eVariationOn.sum_le`.
5. (B) Let $f$ be real with bounded variation on $[a, b]$. Show that the functions $p$ and $q$ of the Jordan decomposition can be chosen bounded on $[a, b]$, and deduce that $f$ is bounded there.
6. (C) Let $f : \mathbb{R} \to \mathbb{R}$ have bounded variation. Show that for each $\varepsilon > 0$ only finitely many points $x$ have $|f(x) - f(x^-)| > \varepsilon$, where $f(x^-)$ is `Function.leftLim f x`. Deduce `BoundedVariationOn.countable_not_continuousAt` for real functions.

### Reference

<?reference?>
