---
title: Real values, almost disjoint sets and quasi measure preserving maps
kind: api
modules:
  - Mathlib.MeasureTheory.Measure.Real
  - Mathlib.MeasureTheory.Measure.AEDisjoint
  - Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
  - Mathlib.MeasureTheory.Measure.MeasuredSets
explains:
  E2: [MeasureTheory.measureReal_def, MeasureTheory.measureReal_union, MeasureTheory.exists_nonempty_inter_of_measureReal_univ_lt_sum_measureReal, MeasureTheory.AEDisjoint.exists_disjoint_diff, MeasureTheory.QuasiMeasurePreserving.ae_eq_comp, MeasureTheory.QuasiMeasurePreserving.exists_preimage_eq_of_preimage_ae, MeasureTheory.MeasuredSets.sub_le_edist]
  E1: auto
families: []
requires: [V13, V18.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Real values, almost disjoint sets and quasi measure preserving maps

### Overview

A measure takes values in `ℝ≥0∞`. This is the right type for the theory, because every set has a measure and countable sums always exist. It is the wrong type for computation with differences, ratios and inequalities, where a student wants real numbers. The first module of this section gives the real-valued version $\mu_{\mathbb{R}}(s)$ of a measure and transfers the rules of Section 1 to it.

The other three modules make the language of Section 3 sharper. Two sets are almost disjoint when their intersection is a null set. A map is quasi measure preserving when the preimage of a null set is a null set; such a map respects every almost everywhere statement. Last, the measurable sets of a space form a metric space for the distance $\mu(s \mathbin{\triangle} t)$, and a generating ring of sets is dense in it.

### The library around it

#### The real-valued measure

For a measure $\mu$ and a set $s$, the real number `μ.real s` is the image of $\mu(s)$ in $\mathbb{R}$. The definition is `MeasureTheory.Measure.real`, and `MeasureTheory.measureReal_def` unfolds it: `μ.real s = (μ s).toReal`. The map `ENNReal.toReal` sends $\infty$ to $0$, so a set of infinite measure has real measure $0$. Every rule for `μ.real` therefore needs a finiteness hypothesis. Mathlib writes this hypothesis as an argument with a default value, `(h : μ s ≠ ∞ := by finiteness)`. For a finite measure the tactic `finiteness` proves it, and the user does not see it.

The names follow the names of Section 1 with the word measure replaced by measureReal. The table lists the main rules.

| Lean name | Statement |
|---|---|
| `MeasureTheory.measureReal_nonneg` | $0 \le \mu_{\mathbb{R}}(s)$ |
| `MeasureTheory.measureReal_mono` | $s_1 \subseteq s_2$, $\mu(s_2) < \infty$ give $\mu_{\mathbb{R}}(s_1) \le \mu_{\mathbb{R}}(s_2)$ |
| `MeasureTheory.measureReal_union` | disjoint, $s_2$ measurable, both finite: $\mu_{\mathbb{R}}(s_1 \cup s_2) = \mu_{\mathbb{R}}(s_1) + \mu_{\mathbb{R}}(s_2)$ |
| `MeasureTheory.measureReal_union_le` | $\mu_{\mathbb{R}}(s_1 \cup s_2) \le \mu_{\mathbb{R}}(s_1) + \mu_{\mathbb{R}}(s_2)$ |
| `MeasureTheory.measureReal_compl` | for finite $\mu$ and measurable $s$: $\mu_{\mathbb{R}}(s^c) = \mu_{\mathbb{R}}(\text{univ}) - \mu_{\mathbb{R}}(s)$ |
| `MeasureTheory.probReal_compl_eq_one_sub` | for a probability measure: $\mu_{\mathbb{R}}(s^c) = 1 - \mu_{\mathbb{R}}(s)$ |
| `MeasureTheory.measureReal_eq_zero_iff` | for $\mu(s) < \infty$: $\mu_{\mathbb{R}}(s) = 0 \iff \mu(s) = 0$ |
| `MeasureTheory.ofReal_measureReal` | for $\mu(s) < \infty$: `ENNReal.ofReal (μ.real s) = μ s` |

The proof of `MeasureTheory.measureReal_union` shows the pattern. The additivity $\mu(s_1 \cup s_2) = \mu(s_1) + \mu(s_2)$ holds in `ℝ≥0∞`. The map `ENNReal.toReal` is additive on finite values, by `ENNReal.toReal_add`. The finiteness hypotheses make this lemma apply. Variants carry suffixes: `₀` for null measurable sets instead of measurable sets, and a prime for the version with the measurability hypothesis on the other set.

The finite sums give a pigeonhole principle for measures. Let $\mu$ be finite and let $t_i$, $i \in s$, be finitely many measurable sets. If they are pairwise disjoint, then $\sum_{i \in s} \mu_{\mathbb{R}}(t_i) \le \mu_{\mathbb{R}}(\text{univ})$, `MeasureTheory.sum_measureReal_le_measureReal_univ`. The contrapositive is `MeasureTheory.exists_nonempty_inter_of_measureReal_univ_lt_sum_measureReal`: if the sum of the measures is larger than the measure of the whole space, then two of the sets meet. The file also adds a `positivity` extension, so `positivity` proves goals of the form `0 ≤ μ.real s`.

#### Almost disjoint sets

The predicate `MeasureTheory.AEDisjoint μ s t` means $\mu(s \cap t) = 0$. It is the natural notion of disjointness for sets that are only defined up to null sets. Disjoint sets are almost disjoint, `Disjoint.aedisjoint`, and a null set is almost disjoint from every set, `MeasureTheory.AEDisjoint.of_null_left`. The relation is symmetric, `MeasureTheory.AEDisjoint.symm`, and it respects finite and countable unions in each argument, `MeasureTheory.AEDisjoint.union_left_iff` and `MeasureTheory.AEDisjoint.iUnion_left_iff`.

An almost disjoint pair becomes a disjoint pair after the removal of a null set, `MeasureTheory.AEDisjoint.exists_disjoint_diff`: there is a measurable null set $u$ with $s \setminus u$ disjoint from $t$. The proof takes for $u$ a measurable null set that contains $s \cap t$, which exists by `MeasureTheory.toMeasurable`. The countable version is `MeasureTheory.exists_null_pairwise_disjoint_sdiff`: for a pairwise almost disjoint family $(s_i)$ there are measurable null sets $t_i$ with the sets $s_i \setminus t_i$ pairwise disjoint. This is the reason that countable additivity, `MeasureTheory.measure_iUnion₀`, holds for pairwise almost disjoint null measurable sets. A last useful rule: removing an almost disjoint set does not change the measure, `MeasureTheory.AEDisjoint.measure_sdiff_left` gives $\mu(s \setminus t) = \mu(s)$.

#### Quasi measure preserving maps

Let $f : \alpha \to \beta$, and let $\mu_a$ and $\mu_b$ be measures on $\alpha$ and $\beta$. The structure `MeasureTheory.QuasiMeasurePreserving f μa μb` holds when $f$ is almost everywhere measurable and the image measure $f_* \mu_a$ is absolutely continuous with respect to $\mu_b$. The constructor is `MeasureTheory.QuasiMeasurePreserving.mk`. In words: the preimage of a $\mu_b$-null set is a $\mu_a$-null set, `MeasureTheory.QuasiMeasurePreserving.preimage_null`. Every measurable map is quasi measure preserving onto its image measure, `Measurable.quasiMeasurePreserving`. A measure preserving map, a linear isomorphism of $\mathbb{R}^n$ and a group translation for a Haar measure are the main examples.

The point of the definition is that almost everywhere statements pull back. If $p$ holds $\mu_b$-almost everywhere, then $p \circ f$ holds $\mu_a$-almost everywhere, `MeasureTheory.QuasiMeasurePreserving.ae`. In the form of a filter, $f$ tends from `ae μa` to `ae μb`, `MeasureTheory.QuasiMeasurePreserving.tendsto_ae`. For functions this gives `MeasureTheory.QuasiMeasurePreserving.ae_eq_comp`:
$$g_1 =_{\mu_b\text{-a.e.}} g_2 \implies g_1 \circ f =_{\mu_a\text{-a.e.}} g_2 \circ f.$$
Proof: the set $\{y \mid g_1(y) \neq g_2(y)\}$ is $\mu_b$-null, and its preimage under $f$ is the set where $g_1 \circ f \neq g_2 \circ f$. The class is closed under composition, `MeasureTheory.QuasiMeasurePreserving.comp`, and an almost everywhere measurable function composed with a quasi measure preserving map is almost everywhere measurable, `AEMeasurable.comp_quasiMeasurePreserving`.

For a self map $f : \alpha \to \alpha$ that is quasi measure preserving for $\mu$, the module studies almost invariant sets, the sets $s$ with $f^{-1}(s) = s$ almost everywhere. Such a set has a strictly invariant version: `MeasureTheory.QuasiMeasurePreserving.exists_preimage_eq_of_preimage_ae` gives a measurable $t$ with $t = s$ almost everywhere and $f^{-1}(t) = t$. The proof takes $t = \limsup_n f^{-n}(s)$. The iterated preimages are all equal to $s$ almost everywhere, so their limit superior is too (`MeasureTheory.QuasiMeasurePreserving.limsup_preimage_iterate_ae_eq`), and the limit superior of a sequence is invariant under the shift $n \mapsto n + 1$. Volume 21 uses this result in ergodic theory. For a group action, `MeasureTheory.pairwise_aedisjoint_of_aedisjoint_forall_ne_one` turns almost disjointness of $g \cdot s$ and $s$ for $g \neq 1$ into pairwise almost disjointness of all translates. The theory of fundamental domains of group actions uses this lemma.

#### The metric space of measurable sets

The type `MeasureTheory.MeasuredSets μ` is the type of measurable sets of $\alpha$, with the extended distance $d(s, t) = \mu(s \mathbin{\triangle} t)$. The triangle inequality is `MeasureTheory.measure_symmDiff_le`. The measure is a 1-Lipschitz function on this space, `MeasureTheory.MeasuredSets.sub_le_edist`: $\mu(s) - \mu(t) \le \mu(s \mathbin{\triangle} t)$. The proof is short: $\mu(s) - \mu(t) \le \mu(s \setminus t)$, and $s \setminus t \subseteq s \mathbin{\triangle} t$. So the measure is continuous, `MeasureTheory.MeasuredSets.continuous_measure`. For a finite measure the real version is `MeasureTheory.MeasuredSets.lipschitzWith_measureReal`.

The main result is an approximation theorem. Let $\mu$ be finite, let $C$ be a ring of sets that generates the σ-algebra, and assume that a countable subfamily of $C$ covers the space up to a null set. Then each measurable set is a limit of members of $C$: `MeasureTheory.exists_measure_symmDiff_lt_of_generateFrom_isSetRing` gives, for each measurable $s$ and each $\varepsilon > 0$, some $t \in C$ with $\mu(t \mathbin{\triangle} s) < \varepsilon$. The proof shows that the sets with this property form a σ-algebra that contains $C$. The topological form is `MeasureTheory.dense_of_generateFrom_isSetRing`, and the versions for a semiring of sets end in isSetSemiring. The covering condition is necessary: on $\{0, 1\}$ with the counting measure, the ring $\{\emptyset, \{0\}\}$ does not approximate $\{1\}$.

#### Common errors

1. Using `μ.real` for a set of infinite measure. Its value is $0$, and the lemmas need $\mu(s) \neq \infty$. When `finiteness` cannot prove this, Lean asks for it as a new goal or fails with an error at the default argument.
2. Confusing `MeasureTheory.AEDisjoint μ s t` with `Disjoint s t`. Countable additivity for almost disjoint sets also needs null measurability; the lemma is `MeasureTheory.measure_iUnion₀`, not `MeasureTheory.measure_iUnion`.
3. Using a quasi measure preserving map to transport measures of sets. The definition controls null sets only. A quasi measure preserving map can change the measure of a set of positive measure; use `MeasureTheory.MeasurePreserving` for equalities of measures.

### Exercises

1. (A) Let $\mu$ be the counting measure on $\mathbb{N}$. Compute `μ.real Set.univ` and explain why `MeasureTheory.measureReal_compl` does not apply.
2. (A) Let $\mu$ be a probability measure and $s_1, s_2, s_3$ measurable sets with $\mu_{\mathbb{R}}(s_i) > 1/3$. Show that two of them meet.
3. (B) Show that $x \mapsto 2x$ on $\mathbb{R}$ is quasi measure preserving for the Lebesgue measure but not measure preserving.
4. (B) Prove `MeasureTheory.QuasiMeasurePreserving.comp` from the definition with null sets.
5. (B) Let $\mu$ be finite. Prove that $s \mapsto \mu(s)$ is continuous on `MeasureTheory.MeasuredSets μ` from `MeasureTheory.MeasuredSets.sub_le_edist`.
6. (C) Use `MeasureTheory.exists_measure_symmDiff_lt_of_generateFrom_isSetRing` to show that each Borel set $s \subseteq [0, 1]$ is approximated in measure by finite unions of intervals.

### Reference

<?reference?>
