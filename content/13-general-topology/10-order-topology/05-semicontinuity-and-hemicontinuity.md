---
title: Semicontinuity and hemicontinuity
kind: api
modules:
  - Mathlib.Topology.Semicontinuity.Defs
  - Mathlib.Topology.Semicontinuity.Basic
  - Mathlib.Topology.Semicontinuity.Hemicontinuity
  - Mathlib.Topology.Semicontinuity.Lindelof
  - Mathlib.Topology.Semicontinuity.Michael
  - Mathlib.Topology.Sion
explains:
  E2: [SemicontinuousAt, LowerSemicontinuous, lowerSemicontinuous_iff_isClosed_preimage, lowerSemicontinuousAt_iff_le_liminf, lowerSemicontinuous_iSup, LowerSemicontinuousOn.exists_isMinOn, LowerHemicontinuous, upperHemicontinuous_iff_forall_isOpen, HasOpenLowerSections.lowerHemicontinuous, "Sion.minimax'"]
  E1: auto
families: []
requires: [V04, V13.C01, V13.C02, V13.C05, V13.C07, V13.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Semicontinuity and hemicontinuity

### Overview

A lower semicontinuous function can jump up but not down: near $x$, its values are at least a little below $f(x)$. The indicator function of an open set, the supremum of a family of continuous functions and the length of a curve as a function of the curve are lower semicontinuous. A lower semicontinuous function on a compact set attains its minimum. This is the form of the extreme value theorem that the calculus of variations and convex analysis use.

Hemicontinuity is the analogue for set-valued maps $x \mapsto F(x) \subseteq Y$, the correspondences of economics and game theory. The library defines both notions as cases of one notion: the semicontinuity of a relation $r(x, y)$, which says that $r(x, y)$ stays true for $x'$ near $x$. This section describes this common definition, the API of semicontinuous functions and of hemicontinuous correspondences, and three deeper theorems: a countable reduction of suprema on Lindelöf spaces, the selection theorem of Michael, and the minimax theorem of Sion.

The text uses the filters of Chapter 2, compactness from Chapter 5, uniform convergence from Chapter 7 and paracompact spaces from Chapter 8. The limits inferior are those of Section 3.

### The library around it

#### One definition for four notions

The module `Mathlib.Topology.Semicontinuity.Defs` starts with a relation $r : \alpha \to \beta \to \mathrm{Prop}$ on a topological space $\alpha$. The relation is semicontinuous at $x$ if each $y$ with $r(x, y)$ satisfies $r(x', y)$ for all $x'$ near $x$:

$$\forall y,\ r(x, y) \implies \forall^\infty x' \in \mathcal{N}(x),\ r(x', y).$$

This is `SemicontinuousAt r x`. The variants `SemicontinuousWithinAt r s x`, `SemicontinuousOn r s` and `Semicontinuous r` follow the pattern of the continuity API. The four main notions of the section are abbreviations for special relations:

| Lean name | Relation $r(x, y)$ |
| --- | --- |
| `LowerSemicontinuous f` | $y < f(x)$ |
| `UpperSemicontinuous f` | $f(x) < y$ |
| `LowerHemicontinuous F` | $y$ is an open set that meets $F(x)$ |
| `UpperHemicontinuous F` | $y$ is a neighbourhood of the set $F(x)$ |
| `HasOpenLowerSections F` | $y \in F(x)$ |

So `LowerSemicontinuous f` says: for each $y < f(x)$, eventually $y < f(x')$ near $x$. Each notion has a form at a point, a form within a set at a point and a form on a set. The generic API proves facts once for all of them, for example that a relation composed with a continuous map is semicontinuous (`Semicontinuous.comp`) and that a constant relation is semicontinuous. The names are generated for each notion, as in `LowerSemicontinuousAt.comp` and `LowerHemicontinuous.const`.

The structure of the correspondences adds two notions with no order. `HasOpenLowerSections F` says that each set $\{x : b \in F(x)\}$ is open, and `HasOpenCGraph F` says that the graph $\{(x, b) : b \in F(x)\}$ is open in $\alpha \times \beta$. An open graph gives open lower sections (`HasOpenCGraph.hasOpenLowerSections`), and open lower sections give lower hemicontinuity (`HasOpenLowerSections.lowerHemicontinuous`). *Proof of the last.* Let $t$ be an open set that meets $F(x)$ at a point $b$. The set $\{x' : b \in F(x')\}$ is an open neighbourhood of $x$, and $F(x')$ meets $t$ at $b$ for each $x'$ in it.

#### Semicontinuous functions

The module `Mathlib.Topology.Semicontinuity.Basic` holds the API of semicontinuous functions to a linear order. The first criterion is closedness of sublevel sets:

$$f \text{ lower semicontinuous} \iff \forall y,\ \{x : f(x) \le y\} \text{ is closed.}$$

This is `lowerSemicontinuous_iff_isClosed_preimage`. *Proof.* The complement of $\{f \le y\}$ is $\{x : y < f(x)\}$. The definition says that this set is a neighbourhood of each of its points, so it is open. The converse is the same argument read backwards. The dual criterion for upper semicontinuity is `upperSemicontinuous_iff_isClosed_preimage`. With a closed-ray topology on the target, lower semicontinuity is the closedness of the epigraph $\{(x, t) : f(x) \le t\}$ (`lowerSemicontinuous_iff_isClosed_epigraph`).

In a complete linear order with the order topology the definition has a form with the limit inferior of Section 3:

$$f \text{ lower semicontinuous at } x \iff f(x) \le \liminf_{x' \to x} f(x').$$

This is `lowerSemicontinuousAt_iff_le_liminf`, and `lowerSemicontinuous_iff_le_liminf` is the global form.

The operations on semicontinuous functions follow the order. A continuous function is lower semicontinuous (`Continuous.lowerSemicontinuous`). The indicator of an open set with a nonnegative value is lower semicontinuous (`IsOpen.lowerSemicontinuous_indicator`), and the indicator of a closed set is upper semicontinuous. A sum of lower semicontinuous functions is lower semicontinuous when the addition is continuous (`LowerSemicontinuous.add`), and the form `LowerSemicontinuous.add'` asks only for continuity of the addition at the values. The negation exchanges lower and upper (`LowerSemicontinuous.neg`). A monotone continuous map keeps lower semicontinuity (`Continuous.comp_lowerSemicontinuous`).

The supremum of any family of lower semicontinuous functions is lower semicontinuous:

$$\Big(\forall i,\ f_i \text{ l.s.c.}\Big) \implies \sup_i f_i \text{ l.s.c.}$$

This is `lowerSemicontinuous_iSup`. *Proof.* Let $y < \sup_i f_i(x)$. Then $y < f_i(x)$ for some $i$, and so $y < f_i(x') \le \sup_j f_j(x')$ for $x'$ near $x$. The conditional form is `lowerSemicontinuousOn_ciSup`, and the forms for finite sums and for sums of series in $[0, \infty]$ are `lowerSemicontinuousAt_sum` and `lowerSemicontinuous_tsum`. Only finite infima keep lower semicontinuity (`LowerSemicontinuous.inf`).

The extreme value theorem holds for lower semicontinuous functions. A lower semicontinuous function on a nonempty compact set attains its minimum:

$$\exists a \in s,\ \forall x \in s,\ f(a) \le f(x).$$

This is `LowerSemicontinuousOn.exists_isMinOn`, and `UpperSemicontinuousOn.exists_isMaxOn` is the dual. *Proof sketch.* The sets $s \cap \{f \le f(x)\}$ for $x \in s$ are closed in $s$, so compact, by `LowerSemicontinuousOn.isCompact_inter_preimage_Iic`. They form a chain, so each finite subfamily has a nonempty intersection. By compactness the whole family has a common point $a$, and $f(a) \le f(x)$ for each $x \in s$. A lower semicontinuous function on a compact set is bounded below (`LowerSemicontinuousOn.bddBelow_of_isCompact`).

#### Hemicontinuity

The module `Mathlib.Topology.Semicontinuity.Hemicontinuity` gives the usual criteria for correspondences. A correspondence $F$ is upper hemicontinuous if and only if, for each $x$ and each open $u \supseteq F(x)$, eventually $F(x') \subseteq u$ near $x$:

$$F \text{ u.h.c.} \iff \forall x,\ \forall u \text{ open},\ F(x) \subseteq u \implies \forall^\infty x',\ F(x') \subseteq u.$$

This is `upperHemicontinuous_iff_forall_isOpen`. It follows from the definition, since the open sets that contain $F(x)$ are cofinal among the neighbourhoods of $F(x)$. The set $\{x : F(x) \subseteq u\}$ is written `F ⁻¹' Set.Iic u` in the library, and `upperHemicontinuous_iff_isOpen_preimage_Iic` says that these sets are open for each open $u$. A lower hemicontinuous correspondence is one for which $\{x : F(x) \cap u \ne \emptyset\}$ is open for each open $u$ (`lowerHemicontinuous_iff_isOpen_inter_nonempty`).

For a single-valued map both notions are continuity: `upperHemicontinuous_singleton_iff` and `lowerHemicontinuous_singleton_iff` state that $x \mapsto \{f(x)\}$ is hemicontinuous if and only if $f$ is continuous. Two results link hemicontinuity to the maps of Chapter 1: a map is open if and only if its fibre correspondence $y \mapsto f^{-1}(y)$ is lower hemicontinuous (`isOpenMap_iff_lowerHemicontinuous`), and it is closed if and only if the same correspondence is upper hemicontinuous (`isClosedMap_iff_upperHemicontinuous`). An upper hemicontinuous correspondence has a closed domain (`UpperHemicontinuous.isClosed_domain`). In a regular space, limits of points of $F(x_n)$ lie in a closed value $F(x_0)$ (`UpperHemicontinuousAt.mem_of_tendsto`). Sequential criteria exist for both notions (`LowerHemicontinuousAt.of_sequences`, `UpperHemicontinuousAt.of_sequences`). A uniform limit of hemicontinuous correspondences is hemicontinuous, under conditions (`TendstoUniformly.lowerHemicontinuous`).

#### Three theorems

The module `Mathlib.Topology.Semicontinuity.Lindelof` reduces suprema to countable ones. Let $X$ be hereditarily Lindelöf, for example second countable, and let the target be a separable densely ordered space. If a set $\mathcal{F}$ of lower semicontinuous functions has a least upper bound $s$, then a countable subset of $\mathcal{F}$ has the same least upper bound. This is `exists_countable_lowerSemicontinuous_isLUB`. The proof covers each set $\{s > q\}$, for $q$ in a countable dense set, with the open sets $\{f > q\}$ and takes a countable subcover.

The module `Mathlib.Topology.Semicontinuity.Michael` proves the selection theorem of Michael. Let $X$ be paracompact and normal, and let $F$ be a lower hemicontinuous correspondence into a complete metrizable locally convex space with nonempty closed convex values. Then $F$ has a continuous selection: a continuous $f$ with $f(x) \in F(x)$ for each $x$. This is `LowerHemicontinuous.exists_continuous_selection`. The first step of the proof is `HasOpenLowerSections.exists_continuous_selection`, for correspondences with open lower sections and convex values. It uses a partition of unity of Chapter 8 to glue local constant choices.

The module `Mathlib.Topology.Sion` proves the minimax theorem of Sion. Let $X$ be a nonempty compact convex set and $Y$ a convex set in real topological vector spaces. Let $f(x, y)$ be lower semicontinuous and quasiconvex in $x$, and upper semicontinuous and quasiconcave in $y$, with values in a complete densely ordered linear order. Then

$$\inf_{x \in X} \sup_{y \in Y} f(x, y) = \sup_{y \in Y} \inf_{x \in X} f(x, y).$$

This is `Sion.minimax'`. The form `Sion.minimax` has no completeness assumption and states the result with greatest lower bounds and least upper bounds. The form `Sion.exists_isSaddlePointOn` gives a saddle point when $Y$ is compact too.

#### Common errors

1. The definition of `LowerSemicontinuous` uses the strict inequality $y < f(x)$. A proof that starts from $\varepsilon > 0$ must first choose $y = f(x) - \varepsilon$. In a general order there is no subtraction, so use the order form.
2. A pointwise limit of continuous functions need not be semicontinuous. The supremum of a family is lower semicontinuous, but the infimum is not, except for finite families (`LowerSemicontinuous.inf`).
3. The two hemicontinuities are not dual to each other under complements. The upper notion is about neighbourhoods of the whole set $F(x)$, and the lower notion is about open sets that meet $F(x)$. Use the criteria `upperHemicontinuous_iff_forall_isOpen` and `lowerHemicontinuous_iff_isOpen_inter_nonempty` to state them.

### Exercises

1. (A) Prove that the indicator function of $(0, 1)$ on $\mathbb{R}$ is lower semicontinuous and not upper semicontinuous.
2. (A) Prove `lowerSemicontinuous_iSup` from the definition, and deduce that $x \mapsto \sup_n |x|^{1/n}$ is lower semicontinuous on $\mathbb{R}$.
3. (B) Prove that a lower semicontinuous function on a nonempty compact space attains its minimum. Use the finite intersection property of Chapter 5.
4. (B) Show that the correspondence $F(x) = [0, 1]$ for $x \ne 0$ and $F(0) = \{0\}$ on $\mathbb{R}$ is upper hemicontinuous and not lower hemicontinuous at 0. Find a correspondence with the opposite behaviour.
5. (B) Prove that a map $f : X \to Y$ is open if and only if the correspondence $y \mapsto f^{-1}(y)$ is lower hemicontinuous.
6. (C) Prove the minimax inequality $\sup_y \inf_x f(x, y) \le \inf_x \sup_y f(x, y)$ for any $f$, and give a function on $[0, 1]^2$ for which the inequality is strict.

### Reference

<?reference?>
