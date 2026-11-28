---
title: Operations on measures
kind: api
modules:
  - Mathlib.MeasureTheory.Measure.MeasureSpace
  - Mathlib.MeasureTheory.Measure.CompleteLattice
  - Mathlib.MeasureTheory.Measure.Module
  - Mathlib.MeasureTheory.Measure.Filter
  - Mathlib.MeasureTheory.Measure.Sum
  - Mathlib.MeasureTheory.Measure.Comap
  - Mathlib.MeasureTheory.Measure.Sub
  - Mathlib.MeasureTheory.Measure.SubFinite
  - Mathlib.MeasureTheory.Measure.Trim
  - Mathlib.MeasureTheory.Measure.Dirac
  - Mathlib.MeasureTheory.Measure.Dirac.Basic
  - Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
  - Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne
  - Mathlib.MeasureTheory.Measure.GiryMonad
explains:
  E2: [MeasureTheory.Measure.sum_apply, MeasureTheory.Measure.comap_apply, MeasureTheory.Measure.sub_def, MeasureTheory.trim_measurableSet_eq, MeasureTheory.Measure.restrict_singleton, MeasureTheory.Measure.isAtom_singleton_iff, MeasureTheory.Measure.cofinite_le_ae, MeasureTheory.Measure.bind_apply, MeasureTheory.Measure.join_apply]
  E1: auto
families: []
requires: [V04, V13, V18.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Operations on measures

### Overview

Section 1 defines a measure and Section 3 defines its image and its restriction. A working analyst needs more ways to make new measures from old ones: the sum of a family, the difference of two measures, a scalar multiple, the infimum and the supremum of a set of measures, the pull back along an injective map, and the restriction of a measure to a smaller σ-algebra. The modules of this section construct these measures and give their values on measurable sets. They also define atoms and atomless measures, zero-one measures, the filter of sets with a complement of finite measure, and the Giry monad, which makes the measures on a space into a measurable space of its own.

Most results here have the same shape. An operation is defined on all sets through the outer measure, and the formula for its value holds for a measurable set. The reader must check the hypothesis `MeasurableSet s` before a rewrite.

### The library around it

#### The module structure and the order

The module `Mathlib.MeasureTheory.Measure.MeasureSpace` only imports the basic files; it is the common import for a file that needs measures. The type `MeasureTheory.Measure α` is an additive commutative monoid and a module over `ℝ≥0∞`. The file `Mathlib.MeasureTheory.Measure.Module` gives the API. The coercion to a function respects the operations: `FunLike.coe_add`, `FunLike.coe_smul` and `FunLike.coe_sum` say that $(\mu + \nu)(s) = \mu(s) + \nu(s)$, $(c \cdot \mu)(s) = c \, \mu(s)$ and the same for a finite sum, for every set $s$. The simp lemmas `add_apply` and `smul_apply` are the pointwise forms. A scalar multiple is zero only in the trivial cases, by `MeasureTheory.Measure.ennreal_smul_eq_zero`: $c \cdot \mu = 0$ if and only if $c = 0$ or $\mu = 0$. For $c \neq 0$ the two measures have the same null sets, so `MeasureTheory.Measure.ae_ennreal_smul_measure_iff` gives the same almost everywhere statements.

The file `Mathlib.MeasureTheory.Measure.CompleteLattice` makes measures a complete lattice. The order is pointwise on measurable sets, `MeasureTheory.Measure.le_iff`: $\mu_1 \le \mu_2$ if and only if $\mu_1(s) \le \mu_2(s)$ for every measurable $s$. The top measure gives the value $\infty$ to every nonempty set, and `MeasureTheory.Measure.add_top` says $\mu + \top = \top$. The infimum of a set of measures is computed from the outer measures, `MeasureTheory.Measure.sInf_apply`. The binary infimum has a concrete formula, `MeasureTheory.Measure.inf_apply`:
$$(\mu \sqcap \nu)(s) = \inf_t \bigl(\mu(t \cap s) + \nu(t^c \cap s)\bigr).$$
The choice $t = s$ gives the value $\mu(s)$ and the choice $t = \emptyset$ gives $\nu(s)$, so the right side is below both measures. Every common lower bound $\rho$ satisfies $\rho(s) = \rho(t \cap s) + \rho(t^c \cap s) \le \mu(t \cap s) + \nu(t^c \cap s)$ for measurable $t$, so $\rho$ is below the right side. The bottom element is the zero measure, and `MeasureTheory.Measure.measure_univ_eq_zero` says that a measure is zero if and only if the whole space has measure zero.

The file `Mathlib.MeasureTheory.Measure.Filter` relates the order to the filter `MeasureTheory.ae`. A smaller measure has more almost everywhere statements, `MeasureTheory.ae_mono`. The filter is trivial only for the zero measure: `MeasureTheory.ae_eq_bot` and `MeasureTheory.ae_neBot`. The same file defines `MeasureTheory.Measure.cofinite`, the filter of sets $s$ with $\mu(s^c) < \infty$ (`MeasureTheory.Measure.mem_cofinite`). Each set of full measure is in this filter, `MeasureTheory.Measure.cofinite_le_ae`. Indeed, if $s \in \operatorname{ae} \mu$ then $\mu(s^c) = 0 < \infty$, so $s$ is in `μ.cofinite`.

#### Sums of measures

The sum of a family $(\mu_i)_{i \in \iota}$ of measures is `MeasureTheory.Measure.sum`. The index type is arbitrary. On a measurable set the value is the sum of the values, `MeasureTheory.Measure.sum_apply`:
$$\Bigl(\sum_i \mu_i\Bigr)(s) = \sum_i \mu_i(s).$$
The proof checks countable additivity: for disjoint measurable sets $s_n$, $\sum_i \mu_i(\bigcup_n s_n) = \sum_i \sum_n \mu_i(s_n)$, and the two sums in `ℝ≥0∞` commute because all terms are nonnegative. For a countable index type the formula holds for every set, `MeasureTheory.Measure.sum_apply_of_countable`. The almost everywhere filter of a countable sum is the infimum of the filters, `MeasureTheory.Measure.ae_sum_iff`. Small cases reduce to the addition: `MeasureTheory.Measure.sum_bool` says that the sum over `Bool` is `μ true + μ false`, and `MeasureTheory.Measure.sum_fintype` gives a finite sum. An s-finite measure is by definition a sum of countably many finite measures, so this file supports the class `MeasureTheory.SFinite` of Section 1.

#### Pull back along an injective map

For $f : \alpha \to \beta$ and a measure $\mu$ on $\beta$, the measure `MeasureTheory.Measure.comap f μ` on $\alpha$ is defined when $f$ is injective and sends measurable sets to null measurable sets. Then `MeasureTheory.Measure.comap_apply` gives $(\operatorname{comap} f \, \mu)(s) = \mu(f(s))$ for measurable $s$. The formula defines a measure because an injective map sends disjoint sets to disjoint sets and $f(\bigcup_n s_n) = \bigcup_n f(s_n)$. When the hypotheses fail, Mathlib gives the value zero, `MeasureTheory.Measure.comap_undef`. This is the same convention as for division by zero. The pull back composes, `MeasureTheory.Measure.comap_comap`, and for a measurable equivalence the pull back is the image under the inverse, `MeasurableEquiv.comap_symm` and `MeasurableEquiv.map_symm`. The linear version is `MeasureTheory.Measure.comapₗ`.

#### The difference of two measures

Measures do not form a group, but `ℝ≥0∞` has a truncated subtraction, and measures have one too. Mathlib defines $\mu - \nu$ as the smallest measure $d$ with $\mu \le d + \nu$, `MeasureTheory.Measure.sub_def`:
$$\mu - \nu = \inf \{ d \mid \mu \le d + \nu \}.$$
This is the definition of a truncated subtraction in an ordered monoid. It gives $\mu - \nu \le \mu$ (`MeasureTheory.Measure.sub_le`) and $\mu - \mu = 0$ (`MeasureTheory.Measure.sub_self`) with no hypothesis. The pointwise formula needs more: if $\nu \le \mu$ and $\nu$ is finite, then `MeasureTheory.Measure.sub_apply` gives $(\mu - \nu)(s) = \mu(s) - \nu(s)$ for measurable $s$, and `MeasureTheory.Measure.sub_add_cancel_of_le` gives $\mu - \nu + \nu = \mu$. The file `Mathlib.MeasureTheory.Measure.SubFinite` treats two finite measures. Then `MeasureTheory.Measure.sub_le_iff_le_add` holds: $\mu - \nu \le \xi$ if and only if $\mu \le \xi + \nu$. The same file proves that a density difference is a difference of measures, `MeasureTheory.Measure.withDensity_sub`. Densities are the subject of Chapter 4.

#### Restriction to a smaller σ-algebra

Let $m \le m_0$ be two σ-algebras on $\alpha$ and let $\mu$ be a measure for $m_0$. The measure `μ.trim hm` is the restriction of $\mu$ to the sets of $m$. It is the main construction of the theory of conditional expectation, where $m$ is a sub-σ-algebra. On an $m$-measurable set the value does not change, `MeasureTheory.trim_measurableSet_eq`. For an arbitrary set the trimmed measure is larger, `MeasureTheory.le_trim`, because its outer measure uses fewer covering sets. A statement almost everywhere for `μ.trim hm` is a statement almost everywhere for $\mu$, `MeasureTheory.ae_of_ae_trim` and `MeasureTheory.ae_le_of_ae_le_trim`. The converse needs measurability for $m$: `ae_eq_trim_of_measurable` says that two $m$-measurable functions equal $\mu$-almost everywhere are equal `μ.trim hm`-almost everywhere. The trim of a σ-finite measure need not be σ-finite. For the trivial σ-algebra, `MeasureTheory.sigmaFinite_trim_bot_iff` says that the trim is σ-finite exactly when $\mu$ is finite.

#### Dirac measures and atoms

The Dirac measure `MeasureTheory.Measure.dirac a` comes from Section 1. The files `Mathlib.MeasureTheory.Measure.Dirac` and `Mathlib.MeasureTheory.Measure.Dirac.Basic` give its properties. An almost everywhere statement for the Dirac measure is a statement at the point, `MeasureTheory.ae_dirac_iff`, when the set of good points is measurable. The image of a Dirac measure is a Dirac measure, `MeasureTheory.Measure.map_dirac`. Two Dirac measures are equal if and only if no measurable set separates the points, `MeasureTheory.dirac_ne_dirac_iff_exists_measurableSet`, and `MeasureTheory.dirac_eq_dirac_iff` turns this into $\delta_x = \delta_y \iff x = y$ for a space where measurable sets separate points. The restriction of a measure to a point is a multiple of the Dirac measure, `MeasureTheory.Measure.restrict_singleton`:
$$\mu|_{\{a\}} = \mu(\{a\}) \cdot \delta_a.$$
To prove it, evaluate both sides at a measurable $s$: the left side is $\mu(s \cap \{a\})$, which is $\mu(\{a\})$ if $a \in s$ and $0$ otherwise. On a countable type with measurable singletons a measure is the sum of its point masses, `MeasureTheory.Measure.sum_smul_dirac`, and two measures that agree on points are equal, `MeasureTheory.Measure.ext_of_singleton`. A Dirac measure and a measure with no point masses are mutually singular, `MeasureTheory.mutuallySingular_dirac`.

An atom of $\mu$ is a measurable set $s$ with $\mu(s) > 0$ such that every subset has measure $0$ or $\mu(s)$; it is the predicate `MeasureTheory.Measure.IsAtom` of `Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms`. The class `MeasureTheory.NoAtoms` says that no set is an atom. With measurable singletons, a point is an atom exactly when it has positive mass, `MeasureTheory.Measure.isAtom_singleton_iff`; a single point has no proper nonempty subsets, so only the condition $\mu(\{x\}) > 0$ remains. The useful form of the class is `MeasureTheory.noAtoms_iff_forall_exists`: every measurable set of positive measure has a measurable subset of strictly smaller positive measure. The file `Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne` defines the opposite extreme, the class `MeasureTheory.IsZeroOneMeasure` of measures with values only $0$ and $1$. Then `MeasureTheory.Measure.zero_one` gives the dichotomy for every set, and `MeasureTheory.IsZeroOneMeasure.measure_inter_eq_prod` says that any two measurable sets are independent: $\mu(s \cap t) = \mu(s)\mu(t)$.

#### The Giry monad

The file `Mathlib.MeasureTheory.Measure.GiryMonad` puts a σ-algebra on `MeasureTheory.Measure α`: the smallest one for which each evaluation $\mu \mapsto \mu(s)$ with $s$ measurable is measurable (`MeasureTheory.Measure.measurable_coe`). A map into measures is measurable when all its evaluations are, `MeasureTheory.Measure.measurable_of_measurable_coe`. The monad has two operations. The join of a measure $m$ on measures is the average of the measures, `MeasureTheory.Measure.join_apply`: $(\operatorname{join} m)(s) = \int^- \mu(s) \, dm(\mu)$. The bind of $m$ with a kernel $f : \alpha \to \operatorname{Measure} \beta$ is `m.bind f`, with `MeasureTheory.Measure.bind_apply`:
$$(m \gg\!= f)(s) = \int^- f(a)(s) \, dm(a).$$
These formulas use the lower Lebesgue integral of Chapter 4. The monad laws hold: `MeasureTheory.Measure.dirac_bind`, `MeasureTheory.Measure.bind_dirac` and `MeasureTheory.Measure.bind_bind`. The join is the bind with the identity, `MeasureTheory.Measure.join_eq_bind`. The integral against a bind is an iterated integral, `MeasureTheory.Measure.lintegral_bind`. Volume 20 builds Markov kernels on this structure.

#### Common errors

1. Rewriting with `MeasureTheory.Measure.sum_apply`, `MeasureTheory.Measure.sub_apply` or `MeasureTheory.trim_measurableSet_eq` on a set with no measurability proof. Each needs `MeasurableSet s`; the trim lemma needs measurability for the small σ-algebra $m$, not for $m_0$.
2. Expecting $(\mu - \nu)(s) = \mu(s) - \nu(s)$ in general. This needs $\nu \le \mu$ and $\nu$ finite. Without these hypotheses the measure `μ - ν` is still defined, by `MeasureTheory.Measure.sub_def`, but its values differ.
3. Using `MeasureTheory.Measure.comap` with a map that is not injective. Lean accepts the term, but its value is the zero measure by `MeasureTheory.Measure.comap_undef`, and every lemma about it asks for injectivity.

### Exercises

1. (A) Let $\mu = \delta_0 + \delta_1$ on $\mathbb{R}$. Compute $(\mu - \delta_0)$ and $(\delta_0 - \mu)$ from `MeasureTheory.Measure.sub_def`.
2. (A) Use `MeasureTheory.Measure.sum_apply` to show that $\sum_{n \in \mathbb{N}} \delta_n$ on $\mathbb{N}$ is the counting measure.
3. (B) Prove `MeasureTheory.Measure.cofinite_le_ae` and give a measure for which the two filters are different.
4. (B) Let $m$ be the trivial σ-algebra $\{\emptyset, \alpha\}$. Describe `μ.trim hm` and show that it is σ-finite if and only if $\mu(\alpha) < \infty$.
5. (B) Show that a zero-one measure $\mu$ on a countable type with measurable singletons is a Dirac measure. Use `MeasureTheory.Measure.sum_smul_dirac`.
6. (C) Prove that the Lebesgue measure on $[0, 1]$ has no atoms: every measurable set $s$ with $\lambda(s) > 0$ has a measurable subset of measure $\lambda(s)/2$. Use the continuity of $t \mapsto \lambda(s \cap [0, t])$.

### Reference

<?reference?>
