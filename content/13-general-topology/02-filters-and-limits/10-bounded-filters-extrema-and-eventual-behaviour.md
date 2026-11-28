---
title: Bounded filters, extrema and eventual behaviour
kind: api
modules:
  - Mathlib.Order.Filter.IsBounded
  - Mathlib.Order.Filter.Extr
  - Mathlib.Order.Filter.EventuallyConst
  - Mathlib.Order.Filter.IndicatorFunction
  - Mathlib.Order.Filter.Interval
  - Mathlib.Order.Filter.TendstoCofinite
  - Mathlib.Order.Filter.ZeroAndBoundedAtFilter
  - Mathlib.Order.Filter.ENNReal
explains:
  E2: [Filter.isBoundedUnder_of, Filter.isBoundedUnder_iff_eventually_bddAbove, Filter.not_isBoundedUnder_of_tendsto_atTop, IsMinFilter, IsMaxOn, isMinOn_iff, Filter.EventuallyConst, Filter.eventuallyConst_atTop, Filter.TendstoIxxClass, Filter.tendstoCofinite_iff_finite_preimage_singleton]
  E1: auto
families: []
requires: [V04, V05, V13.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Bounded filters, extrema and eventual behaviour

### Overview

This section collects several small vocabularies that describe what a function does along a filter. The first is boundedness: a function is bounded above along $l$ if it is eventually below some constant. The limit superior of Volume 4 needs this predicate to make sense in a conditionally complete lattice. The second is local extrema along a filter: $f$ has a minimum at $a$ along $l$ if $f(a) \le f(x)$ for $x$ in a large set of $l$. A local minimum is the case $l = \mathcal{N}(a)$.

The other vocabularies are shorter. A function can be eventually constant. An indicator function can converge pointwise. A family of intervals can tend to a filter. A map can send the cofinite filter into the cofinite filter. A function to a normed space can tend to $0$ or be bounded along a filter. The section ends with the rules for the limit superior in $[0, \infty]$.

### The library around it

#### Bounded and cobounded filters

Let $r$ be a relation on $\alpha$, such as $\le$. The predicate `Filter.IsBounded r f` says that some $b$ satisfies $r(x, b)$ for $x$ in a large set of $f$. For a function $u : \beta \to \alpha$, `Filter.IsBoundedUnder r f u` is `IsBounded r (map u f)`, that is, eventually $r(u(x), b)$. The dual `Filter.IsCobounded r f` says that the set of the eventual bounds is not all of $\alpha$, in a form that is weak enough to hold for each proper filter in a bounded order. The definitions are in `Mathlib.Order.Filter.Defs`, and the API is in `Mathlib.Order.Filter.IsBounded`.

The basic rules are as follows. A function that is bounded on the whole type is bounded along each filter (`Filter.isBoundedUnder_of`). A function is bounded above along $f$ if and only if it is bounded above on some set of $f$ (`Filter.isBoundedUnder_iff_eventually_bddAbove`). A function that tends to `atTop` along a proper filter is not bounded above (`Filter.not_isBoundedUnder_of_tendsto_atTop`). Along the cofinite filter, eventual boundedness in a directed order gives boundedness of the whole range (`Filter.IsBoundedUnder.bddAbove_range_of_cofinite`), because the finitely many exceptional values have an upper bound.

| Lean name | Statement |
|---|---|
| `Filter.isBoundedUnder_of` | a bound for all $x$ gives `IsBoundedUnder r f u` |
| `Filter.IsBoundedUnder.mono` | boundedness passes to a smaller filter |
| `Filter.isBoundedUnder_le_add` | $u$, $v$ bounded above along $f$ give $u + v$ bounded above |
| `Filter.isBoundedUnder_le_sum` | the same for a finite sum |
| `Filter.IsBounded.isCobounded_flip` | bounded for $r$ along a proper filter gives cobounded for the flip of $r$ |
| `Filter.isBounded_le_atBot` | the filter `atBot` is bounded above |
| `Monotone.isBoundedUnder_le_comp` | a monotone map keeps boundedness above |

The bounds matter for the limit superior. The theorem `Filter.limsup_le_of_le` and its relatives in Volume 4 take hypotheses of the form `IsCoboundedUnder (· ≤ ·) f u`. In $\mathbb{R}$, the limit superior of a function that is not bounded above is the junk value $0$ (`Real.limsup_of_not_isBoundedUnder`).

#### Extrema along a filter

The module `Mathlib.Order.Filter.Extr` defines `IsMinFilter f l a`: $f(a) \le f(x)$ for $x$ in a large set of $l$. The predicates `IsMaxFilter` and `IsExtrFilter` are the maximum and the extremum. The forms on a set are `IsMinOn f s a`, which is `IsMinFilter f (𝓟 s) a`, with `IsMaxOn` and `IsExtrOn`. So `isMinOn_iff` says that $f$ has a minimum on $s$ at $a$ if and only if $f(a) \le f(x)$ for each $x \in s$. A local minimum is `IsLocalMin f a`, which is `IsMinFilter f (𝓝 a) a`.

The rules come in families that act on each of the six predicates in the same way.

- Change of the filter: `IsMinFilter.filter_mono` passes to a smaller filter, and `IsMinFilter.filter_inf` to an infimum. The form for sets is `IsMinOn.of_subset`.
- Composition: `IsMinFilter.comp_mono` composes with a monotone map, `IsMinFilter.comp_antitone` exchanges the minimum and the maximum, and `IsMinFilter.comp_of_tendsto` composes with a map along filters.
- Algebra: `IsMinFilter.add` says that a sum of two functions with a minimum at $a$ has a minimum at $a$. The forms `IsMinFilter.neg`, `IsMinFilter.sub`, `IsMinFilter.max` and `IsMinFilter.min` follow the order rules.
- Values: `IsMinOn.isGLB` says that $f(a)$ is the greatest lower bound of $f(s)$, and `IsMinOn.iInf_eq` gives the infimum.

The order dual exchanges the two kinds: `isMinOn_dual_iff` says that $f$ has a minimum as a map to $\beta^{\mathrm{op}}$ if and only if it has a maximum. Monotone functions give extrema at the ends of an interval: `isMinOn_Ici_of_anti_mono` and `isMaxOn_Icc_of_mono_anti` are examples. The theorem of Fermat on critical points uses `IsLocalMin`.

#### Eventually constant functions

The predicate `Filter.EventuallyConst f l` says that $f$ is constant on a large set of $l$. If the codomain is nonempty, this holds if and only if $f$ tends to a point filter (`Filter.eventuallyConst_iff_tendsto`). Along `atTop` it says that the values stop changing: `Filter.eventuallyConst_atTop` gives some $i$ with $f(j) = f(i)$ for $j \ge i$. The property passes to compositions (`Filter.EventuallyConst.comp`), to sums and products, and to smaller filters (`Filter.EventuallyConst.anti`). For a set, `Filter.EventuallyEmptyOrUniv s l` says that eventually $s$ contains all points or none, and this is the condition under which the indicator of $s$ is eventually constant.

#### Indicator functions

The module `Mathlib.Order.Filter.IndicatorFunction` gives the rules for indicators along filters. The rule `Filter.EventuallyEq.indicator` says that $f =ᶠ[l] g$ gives $1_s f =ᶠ[l] 1_s g$. For a monotone family $s_i$ of sets, the indicators converge pointwise to the indicator of the union: `Monotone.tendsto_indicator` states that $1_{s_i} f (a)$ tends to $1_{\bigcup_i s_i} f (a)$ along `atTop`, and in fact it is eventually equal to it. The antitone form `Antitone.tendsto_indicator` gives the intersection. Measure theory uses these results to approximate a set by an increasing sequence of sets.

#### Families of intervals

The class `Filter.TendstoIxxClass Ixx l₁ l₂` says that the intervals $\mathrm{Ixx}(a, b)$ tend to the small sets of $l_2$ when $a$ and $b$ tend to $l_1$. Here Ixx is one of `Set.Icc`, `Set.Ico`, `Set.Ioc` and `Set.Ioo`. With this class, `Filter.Tendsto.Icc` says that if $u_1$ and $u_2$ tend to $l_1$, then $[u_1(x), u_2(x)]$ eventually lies in each set of $l_2$. The instances include `Filter.tendsto_Icc_atTop_atTop` and `Filter.tendsto_Icc_pure_pure`, and the order topology adds instances for the neighbourhood filters. The fundamental theorem of calculus uses this class to treat limits of integrals over intervals of shrinking length.

#### Maps that tend to the cofinite filter

The class `Filter.TendstoCofinite f` says that $f$ tends from the cofinite filter to the cofinite filter. This holds if and only if each fibre $f^{-1}(\{b\})$ is finite (`Filter.tendstoCofinite_iff_finite_preimage_singleton`), and so each injective map has it (`Filter.tendstoCofinite_of_injective`). The class is stable under composition (`Filter.TendstoCofinite.comp`). It lets a finitely supported function be pushed forward along $f$ with `Filter.TendstoCofinite.mapDomain`.

#### Functions that tend to zero or are bounded

For a filter $l$ on $\alpha$ and a function $f : \alpha \to \beta$, `Filter.ZeroAtFilter l f` says that $f$ tends to $0$ along $l$, and, for a normed codomain, `Filter.BoundedAtFilter l f` says that $\|f\|$ is $O(1)$ along $l$. The rules are linear: `Filter.ZeroAtFilter.add`, `Filter.BoundedAtFilter.add` and the scalar forms. A function that tends to zero times a bounded function tends to zero (`Filter.ZeroAtFilter.mul_boundedAtFilter`). The definitions `Filter.zeroAtFilterSubmodule` and `Filter.boundedFilterSubalgebra` pack these classes as a submodule and a subalgebra. The theory of modular forms uses them, because a modular form must be bounded at the cusps.

#### The limit superior in the extended nonnegative reals

The module `Mathlib.Order.Filter.ENNReal` gives the arithmetic of `Filter.limsup` in $[0, \infty]$. Multiplication by a finite constant commutes with the limit superior (`ENNReal.limsup_const_mul_of_ne_top`). For a filter with countable intersections, the limit superior of a sum is at most the sum of the limits superior (`ENNReal.limsup_add_le`), and the function is eventually below its limit superior (`ENNReal.eventually_le_limsup`). The countable intersections are needed because the bound uses countably many sets: one for each rational number above the limit superior. Measure theory uses these rules with the almost everywhere filter.

#### Common errors

1. The bound predicates take a relation as an argument. A goal with `IsBoundedUnder (· ≤ ·) f u` asks for an upper bound, and `IsBoundedUnder (· ≥ ·) f u` asks for a lower bound. A lemma for one form does not apply to the other.
2. The predicate `IsMinOn f s a` does not contain $a \in s$. A lemma such as `IsMinOn.isGLB` takes $a \in s$ as a separate hypothesis.
3. In $\mathbb{R}$, the limit superior of an unbounded function is $0$ by convention. Check the boundedness hypotheses before a rewrite with a limit superior.

### Exercises

1. (A) Prove `Filter.isBoundedUnder_of` from the definition of `Filter.IsBoundedUnder`.
2. (A) Show that $x \mapsto x^2$ has `IsMinOn` on $\mathbb{R}$ at $0$, and that it has no maximum on $\mathbb{R}$.
3. (B) Prove `Filter.not_isBoundedUnder_of_tendsto_atTop`.
4. (B) Show that a sequence of natural numbers that is monotone and bounded above is eventually constant, in the form `Filter.EventuallyConst u atTop`.
5. (B) Show that $n \mapsto n^2$ from $\mathbb{Z}$ to $\mathbb{Z}$ has `Filter.TendstoCofinite`, and that it is not injective.
6. (C) Let $s_n$ be an increasing sequence of sets with union $s$. Prove `Monotone.tendsto_indicator` for the constant function $1$, and show that the convergence is eventual equality at each point.

### Reference

<?reference?>
