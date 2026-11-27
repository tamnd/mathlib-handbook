---
title: Complete metric spaces and the Baire category theorem
kind: theory
modules:
  - Mathlib.Topology.MetricSpace.Cauchy
  - Mathlib.Topology.Baire.Lemmas
  - Mathlib.Topology.Baire.CompleteMetrizable
  - Mathlib.Topology.GDelta.Basic
explains:
  E3: [BaireSpace, IsGδ, IsNowhereDense, IsMeagre]
  E2: [Metric.cauchySeq_iff, Metric.cauchySeq_iff', Metric.complete_of_cauchySeq_tendsto, Metric.complete_of_convergent_controlled_sequences, BaireSpace.baire_property, BaireSpace.of_completelyPseudoMetrizable, PseudoMetricSpace.toIsCompletelyPseudoMetrizableSpace, BaireSpace.of_t2Space_locallyCompactSpace, dense_iInter_of_isOpen_nat, dense_iInter_of_isOpen, dense_sInter_of_isOpen, nonempty_interior_of_iUnion_of_closed, dense_iUnion_interior_of_closed, Dense.inter_of_Gδ, isGδ_iff_eq_iInter_nat, residual]
  E1: auto
families: []
requires: [V02, V03, V13.C01, V13.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Complete metric spaces and the Baire category theorem

### Overview

A Cauchy sequence is a sequence whose terms come close to each other. In $\mathbb{R}$ each Cauchy sequence converges; in $\mathbb{Q}$ some do not. A metric space is complete if each Cauchy sequence converges. Completeness is a property of the metric, not of the topology alone, and Chapter 7 puts it in its natural frame, the uniform spaces.

The Baire category theorem is the first deep consequence of completeness. It says that in a complete metric space a countable intersection of dense open sets is dense. Equivalently, the space is not a countable union of closed sets with empty interior. The theorem gives existence proofs without a construction: a property that holds on a countable intersection of dense open sets holds at some point, and in fact on a dense set of points.

### Definitions

**Definition (Cauchy sequence, complete metric space).** A sequence $(x_n)$ in a pseudometric space is Cauchy if for each $\varepsilon > 0$ there is an $N$ with $d(x_m, x_n) < \varepsilon$ for all $m, n \ge N$. The space is complete if each Cauchy sequence converges.

::: mathlib
`Metric.cauchySeq_iff` · `Mathlib.Topology.MetricSpace.Cauchy`

In Mathlib, `CauchySeq u` is defined for a uniform space as `Cauchy (map u atTop)`, a filter statement of Chapter 7. This lemma is the $\varepsilon$-$N$ form in a pseudometric space. The variant `Metric.cauchySeq_iff'` compares each term with the term of index `N`: `dist (u n) (u N) < ε` for `n ≥ N`.

<?decl Metric.cauchySeq_iff?>
:::

::: mathlib
`Metric.cauchySeq_iff'` · `Mathlib.Topology.MetricSpace.Cauchy`

The form of the Cauchy condition with a base term.

<?decl Metric.cauchySeq_iff'?>
:::

::: mathlib
`Metric.complete_of_cauchySeq_tendsto` · `Mathlib.Topology.MetricSpace.Cauchy`

The class `CompleteSpace` is defined with Cauchy filters (Chapter 7). This lemma proves an instance from the sequential definition of the text. In a metric space the two definitions agree, because the uniformity has a countable basis.

<?decl Metric.complete_of_cauchySeq_tendsto?>
:::

::: mathlib
`Metric.complete_of_convergent_controlled_sequences` · `Mathlib.Topology.MetricSpace.Cauchy`

A sharper criterion: it suffices that each sequence with `dist (u n) (u m) < B N` for `m, n ≥ N` converges, for one fixed positive sequence `B`. A proof of completeness often takes `B N = 2⁻¹ ^ N`.

<?decl Metric.complete_of_convergent_controlled_sequences?>
:::

**Definition (Nowhere dense, meagre, $G_\delta$).** Let $X$ be a topological space. A set $A$ is nowhere dense if its closure has empty interior. It is meagre, or of first category, if it is a countable union of nowhere dense sets. A set is a $G_\delta$ set if it is a countable intersection of open sets. A set is residual, or comeagre, if it contains a countable intersection of dense open sets.

::: mathlib
`IsNowhereDense` · `Mathlib.Topology.GDelta.Basic`

`IsNowhereDense s` is `interior (closure s) = ∅`.

<?decl IsNowhereDense?>
:::

::: mathlib
`IsMeagre` · `Mathlib.Topology.GDelta.Basic`

`IsMeagre s` is defined as `sᶜ ∈ residual X`: the complement of a meagre set is residual. The definition uses the filter `residual X`, so the countable union property follows from the filter axioms and countable intersections.

<?decl IsMeagre?>
:::

::: mathlib
`residual` · `Mathlib.Topology.GDelta.Basic`

The filter of residual sets. It is generated, with countable intersections, by the dense open sets, so it is closed under countable intersections by construction. In a Baire space each residual set is dense.

<?decl residual?>
:::

::: mathlib
`IsGδ` · `Mathlib.Topology.GDelta.Basic`

`IsGδ s` says that `s` is the intersection of a countable family of open sets. The lemma `isGδ_iff_eq_iInter_nat` gives the form with a sequence of open sets.

<?decl IsGδ?>
:::

::: mathlib
`isGδ_iff_eq_iInter_nat` · `Mathlib.Topology.GDelta.Basic`

A $G_\delta$ set is an intersection of a sequence of open sets.

<?decl isGδ_iff_eq_iInter_nat?>
:::

**Definition (Baire space).** A topological space $X$ is a Baire space if for each sequence $(U_n)$ of dense open subsets of $X$, the intersection $\bigcap_n U_n$ is dense.

::: mathlib
`BaireSpace` · `Mathlib.Topology.Defs.Basic`

A class with one field, `baire_property`, the definition of the text. The lemmas in `Mathlib.Topology.Baire.Lemmas` derive the other forms.

<?decl BaireSpace?>
:::

::: mathlib
`BaireSpace.baire_property` · `Mathlib.Topology.Defs.Basic`

The defining property, for a sequence of dense open sets.

<?decl BaireSpace.baire_property?>
:::

### Theorems and proofs

**Theorem (Baire category theorem).** A complete pseudometric space is a Baire space.

*Proof.* Let $(U_n)$ be dense open sets in the complete space $X$. A set is dense if it meets each nonempty open set (Chapter 1). So let $W$ be a nonempty open set. The task is to find a point of $W \cap \bigcap_n U_n$.

Step 1. Since $U_0$ is dense and open, $W \cap U_0$ is nonempty and open. Choose $x_0$ in it and $0 < r_0 < 1$ with $\bar B(x_0, r_0) \subseteq W \cap U_0$. This is possible: some ball $B(x_0, s)$ lies in $W \cap U_0$, and $r_0 = \min(s/2, 1/2)$ works.

Step 2. Assume $x_n$ and $r_n > 0$ are chosen. The set $B(x_n, r_n) \cap U_{n+1}$ is nonempty and open, since $U_{n+1}$ is dense and open. As in step 1, choose $x_{n+1}$ in it and $0 < r_{n+1} < r_n / 2$ with $\bar B(x_{n+1}, r_{n+1}) \subseteq B(x_n, r_n) \cap U_{n+1}$.

The balls are nested: $\bar B(x_m, r_m) \subseteq \bar B(x_n, r_n)$ for $m \ge n$. Also $r_n < 2^{-n}$.

Step 3. The sequence $(x_n)$ is Cauchy. For $m \ge n$, $x_m \in \bar B(x_n, r_n)$, so $d(x_m, x_n) \le r_n < 2^{-n}$. Given $\varepsilon > 0$, choose $N$ with $2^{-N} < \varepsilon / 2$. For $m, n \ge N$, $d(x_m, x_n) \le d(x_m, x_N) + d(x_N, x_n) < \varepsilon$.

Step 4. By completeness, $x_n \to x$ for some $x$. Fix $n$. For $m \ge n$, $x_m$ lies in the closed set $\bar B(x_n, r_n)$, so the limit $x$ lies in it too. So $x \in \bar B(x_n, r_n) \subseteq U_n$ for each $n$, and $x \in \bar B(x_0, r_0) \subseteq W$. $\square$

::: mathlib
`BaireSpace.of_completelyPseudoMetrizable` · `Mathlib.Topology.Baire.CompleteMetrizable`

The theorem, as an instance for each completely pseudometrizable space. A complete pseudometric space is one by the instance `PseudoMetricSpace.toIsCompletelyPseudoMetrizableSpace`, so `ℝ` is a Baire space by instance search.

<?decl BaireSpace.of_completelyPseudoMetrizable?>
:::

::: mathlib
`PseudoMetricSpace.toIsCompletelyPseudoMetrizableSpace` · `Mathlib.Topology.Metrizable.CompletelyMetrizable`

A complete pseudometric space is completely pseudometrizable.

<?decl PseudoMetricSpace.toIsCompletelyPseudoMetrizableSpace?>
:::

::: mathlib
`BaireSpace.of_t2Space_locallyCompactSpace` · `Mathlib.Topology.Baire.LocallyCompactRegular`

The other Baire theorem: a locally compact Hausdorff space is a Baire space. The proof replaces the nested balls by nested compact sets and uses the finite intersection property of Chapter 5.

<?decl BaireSpace.of_t2Space_locallyCompactSpace?>
:::

**Corollary (Forms of the Baire property).** Let $X$ be a nonempty Baire space.

1. If $X = \bigcup_n F_n$ with each $F_n$ closed, then some $F_n$ has nonempty interior.
2. $X$ is not meagre in itself.
3. The intersection of two dense $G_\delta$ sets is a dense $G_\delta$ set.

*Proof.* (1) Suppose that each $F_n$ has empty interior. Then $U_n = X \setminus F_n$ is open and dense: an open set that misses $U_n$ lies in $F_n$, so it is empty. By the Baire property $\bigcap_n U_n$ is dense, so nonempty since $X$ is nonempty. But $\bigcap_n U_n = X \setminus \bigcup_n F_n = \emptyset$, a contradiction.

(2) If $X = \bigcup_n A_n$ with $A_n$ nowhere dense, then $X = \bigcup_n \overline{A_n}$ with closed sets of empty interior, against 1.

(3) Let $S = \bigcap_n U_n$ and $T = \bigcap_n V_n$ be dense with $U_n$ and $V_n$ open. Then each $U_n \supseteq S$ and $V_n \supseteq T$ is dense. So $S \cap T$ is the countable intersection of the dense open sets $U_n$ and $V_n$, which is dense by the Baire property. $\square$

::: mathlib
`nonempty_interior_of_iUnion_of_closed` · `Mathlib.Topology.Baire.Lemmas`

Part 1 of the corollary, for any countable index type.

<?decl nonempty_interior_of_iUnion_of_closed?>
:::

::: mathlib
`dense_iUnion_interior_of_closed` · `Mathlib.Topology.Baire.Lemmas`

A stronger form of part 1: if a countable family of closed sets covers `X`, then the union of their interiors is dense.

<?decl dense_iUnion_interior_of_closed?>
:::

::: mathlib
`Dense.inter_of_Gδ` · `Mathlib.Topology.Baire.Lemmas`

Part 3 of the corollary.

<?decl Dense.inter_of_Gδ?>
:::

::: mathlib
`dense_iInter_of_isOpen_nat` · `Mathlib.Topology.Baire.Lemmas`

The Baire property for a sequence. The variants `dense_iInter_of_isOpen` for a countable index type and `dense_sInter_of_isOpen` for a countable set of sets have the same content.

<?decl dense_iInter_of_isOpen_nat?>
:::

::: mathlib
`dense_iInter_of_isOpen` · `Mathlib.Topology.Baire.Lemmas`

The Baire property for a countable index type.

<?decl dense_iInter_of_isOpen?>
:::

::: mathlib
`dense_sInter_of_isOpen` · `Mathlib.Topology.Baire.Lemmas`

The Baire property for a countable set of open sets.

<?decl dense_sInter_of_isOpen?>
:::

### Examples

**Example ($\mathbb{R}$ is uncountable).** The space $\mathbb{R}$ is complete and nonempty, so it is a Baire space. If $\mathbb{R} = \{q_0, q_1, \dots\}$ were countable, then $\mathbb{R} = \bigcup_n \{q_n\}$ with closed sets of empty interior, against part 1 of the corollary. The same argument shows that a nonempty complete metric space without isolated points is uncountable.

**Counterexample ($\mathbb{Q}$ is not a Baire space).** The space $\mathbb{Q}$ is countable, and $\mathbb{Q} = \bigcup_{q \in \mathbb{Q}} \{q\}$. Each $\{q\}$ is closed in $\mathbb{Q}$ and has empty interior, since each interval around $q$ contains other rationals. By part 1 of the corollary, $\mathbb{Q}$ is not a Baire space. By the theorem, $\mathbb{Q}$ with the usual metric is not complete. Chapter 7 gives a direct proof.

**Example ($\mathbb{Q}$ is not a $G_\delta$ set in $\mathbb{R}$).** Suppose $\mathbb{Q} = \bigcap_n U_n$ with $U_n$ open in $\mathbb{R}$. Each $U_n$ contains $\mathbb{Q}$ and is dense. For each $q \in \mathbb{Q}$, the set $\mathbb{R} \setminus \{q\}$ is dense and open. The countable family of the $U_n$ and the $\mathbb{R} \setminus \{q\}$ has an intersection that is dense by Baire, but this intersection is $\mathbb{Q} \setminus \mathbb{Q} = \emptyset$. So $\mathbb{Q}$ is not a $G_\delta$ set, and the irrationals are not a countable union of closed sets.

**Example (Continuity points).** For each $f : \mathbb{R} \to \mathbb{R}$, the set of points of continuity of $f$ is a $G_\delta$ set: it is $\bigcap_n \{x : \text{the oscillation of } f \text{ at } x \text{ is} < 1/n\}$, and each of these sets is open. By the last example, no $f$ is continuous exactly at the rationals. The function of Thomae, $f(p/q) = 1/q$ in lowest terms and $f = 0$ on the irrationals, is continuous exactly at the irrationals.

### The library around it

The class `BaireSpace` is in `Mathlib.Topology.Defs.Basic`. Its consequences are in `Mathlib.Topology.Baire.Lemmas`, and the two instances are in `Mathlib.Topology.Baire.CompleteMetrizable` and `Mathlib.Topology.Baire.LocallyCompactRegular`. The notions $G_\delta$, nowhere dense and meagre are in `Mathlib.Topology.GDelta.Basic`, with the metrizable facts, such as the $G_\delta$ property of the set of continuity points `IsGδ.setOf_continuousAt`, in `Mathlib.Topology.GDelta.MetrizableSpace`.

Mathlib states the Baire theorem for `IsCompletelyPseudoMetrizableSpace`, a property of a topology: it has some complete compatible pseudometric. This makes the theorem apply to open subsets of complete spaces, which are completely metrizable for another metric. The open interval $(0, 1)$ is not complete for the metric of $\mathbb{R}$, but it is homeomorphic to $\mathbb{R}$, so it is a Baire space.

The reference table at the end of the section lists the declarations of the modules.

### Exercises

1. (A) Show that a convergent sequence is Cauchy, and that a Cauchy sequence is bounded.
2. (A) Show that a Cauchy sequence with a convergent subsequence converges.
3. (A) Show that a closed subset of a complete metric space is complete, and that a complete subset of a metric space is closed.
4. (B) Show that the discrete metric space is complete, and that $\mathbb{N}$ with $d(m, n) = |1/m - 1/n|$, $m, n \ge 1$, is not complete, although it has the discrete topology.
5. (B) Show that a nonempty open subset of a Baire space is a Baire space.
6. (B) Show that a set is nowhere dense if and only if its complement contains a dense open set.
7. (C) Let $X$ be a complete metric space and $(f_n)$ continuous maps $X \to \mathbb{R}$ with $\sup_n |f_n(x)| < \infty$ for each $x$. Show that there is a nonempty open set on which the $f_n$ are uniformly bounded. Hint: apply part 1 of the corollary to $F_k = \{x : |f_n(x)| \le k \text{ for all } n\}$.

### Notes and history

The theorem is due to Baire, in his thesis of 1899, for $\mathbb{R}^n$. Osgood had proved the case of $\mathbb{R}$ in 1897. The general form for complete metric spaces is due to Hausdorff (1914), and the name "category" is Baire's: a meagre set is of the first category, and a set that is not meagre is of the second category. Exercise 7 is the principle of uniform boundedness in its most general form; the Banach-Steinhaus theorem of functional analysis is its linear case.

### Reference

<?reference?>
