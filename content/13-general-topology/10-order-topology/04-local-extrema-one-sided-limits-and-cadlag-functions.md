---
title: Local extrema, one-sided limits and càdlàg functions
kind: api
modules:
  - Mathlib.Topology.Order.LocalExtr
  - Mathlib.Topology.Order.ExtrClosure
  - Mathlib.Topology.Order.OrderClosedExtr
  - Mathlib.Topology.Order.Rolle
  - Mathlib.Topology.Order.LeftRightLim
  - Mathlib.Topology.Order.Cadlag
explains:
  E2: [IsLocalMin, IsLocalMinOn.isLocalMin, IsLocalMin.comp_continuous, IsLocalMinOn.closure, isLocalMax_of_mono_anti, exists_Ioo_extr_on_Icc, Function.leftLim, Monotone.continuousAt_iff_leftLim_eq_rightLim, IsRightContinuous, IsCadlag]
  E1: auto
families: []
requires: [V04, V13.C01, V13.C02, V13.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Local extrema, one-sided limits and càdlàg functions

### Overview

A local minimum of a function is a point where the function is smallest on some neighbourhood. Calculus uses local extrema in the Fermat theorem and in the Rolle theorem. The topological part of these results needs no derivative: it needs only the neighbourhood filter of the source and an order on the target. This section describes the definitions of local extrema in the library, their algebra, and the topological form of the Rolle theorem.

The second half of the section treats the one-sided limits of a function on a linear order, as total functions `Function.leftLim` and `Function.rightLim`, and the càdlàg functions: the functions that are right continuous and have left limits at each point. The theory of stochastic processes uses càdlàg paths.

The text uses the filters of Chapter 2, the order topology of Section 1 and the one-sided filters of Section 2. The theorem that a continuous function on a compact set has a maximum is in Chapter 5. The definitions `IsMinOn` and `IsMaxOn` for global extrema on a set are in Volume 4.

### The library around it

#### Local extrema

The module `Mathlib.Topology.Order.LocalExtr` defines the local versions of the extrema of Volume 4. For $f : \alpha \to \beta$ with $\beta$ a preorder:

- `IsLocalMin f a` says that $f(a) \le f(x)$ for all $x$ in some neighbourhood of $a$;
- `IsLocalMinOn f s a` says the same for $x$ near $a$ in $s$;
- `IsLocalMax`, `IsLocalMaxOn`, `IsLocalExtr` and `IsLocalExtrOn` are the variants for maxima and for both.

Each of them is an instance of the filter notion `IsMinFilter` of Volume 4, with the filter `nhds a` or the filter of $a$ within $s$. So the API is the filter API with a fixed filter. A local minimum on $s$ is a local minimum when $s$ is a neighbourhood of $a$ (`IsLocalMinOn.isLocalMin`), and a minimum on a neighbourhood is a local minimum (`IsMinOn.isLocalMin`). On the whole space the two notions agree (`isLocalExtrOn_univ_iff`), and a smaller set keeps the property (`IsLocalMinOn.inter`).

The algebra of local extrema follows the algebra of inequalities. A sum of two functions with a local minimum at $a$ has a local minimum at $a$ (`IsLocalMin.add`). A negation exchanges minima and maxima (`IsLocalMin.neg`). The maximum and minimum of two functions keep the property (`IsLocalMin.max`, `IsLocalMin.min`). Two lemmas compose with other maps:

- if $f$ has a local minimum at $g(b)$ and $g$ is continuous at $b$, then $f \circ g$ has a local minimum at $b$ (`IsLocalMin.comp_continuous`);
- if $f$ has a local minimum at $a$ and $g$ is monotone, then $g \circ f$ has a local minimum at $a$ (`IsLocalMin.comp_mono`).

*Proof of the first.* The minimum gives a neighbourhood $U$ of $g(b)$ on which $f \ge f(g(b))$. Continuity of $g$ at $b$ makes $g^{-1}(U)$ a neighbourhood of $b$, and on it $f \circ g \ge f(g(b))$. Equality near the point transfers the property (`Filter.EventuallyEq.isLocalMin_iff`), and an eventual inequality with equality at the point too (`Filter.EventuallyLE.isLocalMax`). A local extremum blocks openness: the image of a neighbourhood of a local extremum is not a neighbourhood of the value, when the target has points on both sides (`IsLocalExtrOn.not_nhds_le_map`). This is the topological core of the Fermat theorem.

The module `Mathlib.Topology.Order.ExtrClosure` passes extrema to the closure. If $f$ has a local minimum on $s$ at $a$ and $f$ is continuous on $\overline{s}$, then $f$ has a local minimum on $\overline{s}$ at $a$. This is `IsLocalMinOn.closure`, and `IsMinOn.closure` is the global form. *Proof.* The set $\{x : f(a) \le f(x)\}$ is relatively closed in $\overline{s}$ by `isClosed_le` of Section 1, and it contains $s$ near $a$, so it contains $\overline{s}$ near $a$. The target must be order-closed.

The module `Mathlib.Topology.Order.OrderClosedExtr` gives the criterion from monotony. If $f$ is monotone on $(a, b]$ and antitone on $[b, c)$, then $f$ has a local maximum at $b$. This is `isLocalMax_of_mono_anti`, and `isLocalMin_of_anti_mono` is the dual. The proof is direct: the interval $(a, c)$ is a neighbourhood of $b$, and on it each value is at most $f(b)$ by the two monotony hypotheses.

#### The topological Rolle theorem

The module `Mathlib.Topology.Order.Rolle` holds the part of the Rolle theorem that needs no derivative. Let $X$ be densely ordered, let $f$ be continuous on $[a, b]$ with $a < b$ and $f(a) = f(b)$. Then there is $c \in (a, b)$ at which $f$ has an extremum on $[a, b]$:

$$\exists c \in (a, b),\ \text{IsExtrOn}\ f\ [a, b]\ c.$$

This is `exists_Ioo_extr_on_Icc`. *Proof.* The interval $[a, b]$ is compact by Chapter 5, so $f$ has a minimum at some $c$ and a maximum at some $c'$ on it. If one of them lies in $(a, b)$, it is the point. Otherwise both lie in $\{a, b\}$, so the minimum and the maximum are both equal to $f(a) = f(b)$. Then $f$ is constant on $[a, b]$, and each point of $(a, b)$ works. The interval $(a, b)$ is nonempty because $X$ is densely ordered. The interior point gives a local extremum (`exists_isLocalExtr_Ioo`). The form `exists_isLocalExtr_Ioo_of_tendsto` replaces the values at the ends by limits of $f$ at the ends of an open interval. The forms with uIoo in the name allow $b < a$. The Rolle theorem for derivatives follows from these results and the Fermat theorem.

#### Left and right limits as functions

The module `Mathlib.Topology.Order.LeftRightLim` defines the left limit `Function.leftLim f a` of $f : \alpha \to \beta$ at $a$, where $\alpha$ is a linear order. It is the limit of $f$ at $a$ within $(-\infty, a)$ when this limit exists and the filter is proper, and $f(a)$ in the other case. The right limit `Function.rightLim` is the dual. With a limit $y$ the definition gives $y$ in a Hausdorff target (`leftLim_eq_of_tendsto`). A continuous function from the left has $f(a)$ as left limit (`ContinuousWithinAt.leftLim_eq`).

For a monotone function the left limit always exists, and it is the supremum of the values to the left:

$$\lim_{x \to a^-} f(x) = \sup f((-\infty, a)).$$

This is `Monotone.leftLim_eq_sSup`, with the limit statement `Monotone.tendsto_leftLim`. The left limit is a monotone function (`Monotone.leftLim`), it lies below $f$ (`Monotone.leftLim_le`), and left limits lie below right limits at larger points (`Monotone.leftLim_le_rightLim`). A monotone function is continuous at $a$ if and only if its two limits agree:

$$f \text{ continuous at } a \iff \lim_{x \to a^-} f(x) = \lim_{x \to a^+} f(x).$$

This is `Monotone.continuousAt_iff_leftLim_eq_rightLim`. *Proof.* If the limits agree, then $f(a)$ lies between them by monotony, so the two one-sided limits both equal $f(a)$, and continuity follows from `continuousAt_iff_continuous_left_right` of Section 2. Conversely, continuity at $a$ makes both one-sided limits equal to $f(a)$. Each property has an antitone form with the prefix `Antitone`. When the left limit exists in a regular target, the left limit of the function `Function.leftLim f` at $a$ is again the left limit of $f$ (`leftLim_leftLim`), and the left limit of `Function.rightLim f` at $a$ is the left limit of $f$ too (`leftLim_rightLim`).

#### Right continuity and càdlàg functions

The module `Mathlib.Topology.Order.Cadlag` defines the regularity conditions of stochastic processes. The predicate `IsRightContinuous f` says that $f$ is continuous at each $a$ within $(a, \infty)$. On a set, `IsRightContinuousOn f s` asks for continuity within $s \cap (a, \infty)$. The structure `IsCadlag f` asks for right continuity and for the existence of a left limit at each point; its constructor is `IsCadlag.mk`. The dual notions are `IsLeftContinuous` and `IsCaglad`. The library builds the left forms from the right forms with the order dual.

A continuous function is càdlàg (`Continuous.isCadlag`). The class is stable under the operations of a topological group or a topological monoid: `IsCadlag.add`, `IsCadlag.mul`, `IsCadlag.sub` and `IsCadlag.const_smul`. A càdlàg function followed by a continuous function is càdlàg (`IsCadlag.continuous_comp`). With the order topology, a càdlàg function tends to its left limit from the left (`IsCadlag.tendsto_nhdsLT_leftLim`). In a pseudometric target each càdlàg function is locally bounded (`IsCadlag.isLocallyBounded`). In a second countable source the range of a right continuous function is separable (`IsRightContinuous.separableSpace_range`). On an open set, right continuity on the set is right continuity at each point of it (`IsOpen.isRightContinuousOn_iff`).

#### Common errors

1. The predicate `IsLocalMin f a` uses the neighbourhood filter of the whole space. A minimum of a function on $\mathbb{R}$ at the end $a$ of $[a, b]$ is in general not a local minimum. Use `IsLocalMinOn f (Set.Icc a b) a` for it, and pass to `IsLocalMin` with `IsLocalMinOn.isLocalMin` only at an interior point.
2. The value `Function.leftLim f a` is $f(a)$ when the left limit does not exist, so a rewrite with it proves nothing about limits. Prove first that the limit exists, for example with `Monotone.tendsto_leftLim`, and use `leftLim_eq_of_tendsto` after.
3. The definition of `Function.leftLim` uses the order topology of $\alpha$, not the topology of the instance. For a type with another topology the left limit can differ from the limit within `Set.Iio a`.

### Exercises

1. (A) Prove that $x \mapsto x^2$ has a local minimum at 0 on $\mathbb{R}$, and deduce with `IsLocalMin.comp_continuous` that $t \mapsto \sin^2 t$ has a local minimum at 0.
2. (A) Compute `Function.leftLim` and `Function.rightLim` of the indicator function of $[0, \infty)$ at 0, and say if it is càdlàg.
3. (B) Prove `isLocalMax_of_mono_anti` from the definitions.
4. (B) Prove the topological Rolle theorem for $f : [a, b] \to \mathbb{R}$ with $f(a) = f(b)$, using the extreme value theorem.
5. (B) Prove that a monotone function $f : \mathbb{R} \to \mathbb{R}$ is continuous at $a$ if and only if its left and right limits at $a$ agree.
6. (C) Prove that a càdlàg function $f : [0, 1] \to \mathbb{R}$ is bounded, and that for each $\varepsilon > 0$ it has only finitely many jumps of size greater than $\varepsilon$.

### Reference

<?reference?>
