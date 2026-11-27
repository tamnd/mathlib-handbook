---
title: Conservative maps and Poincaré recurrence
kind: theory
modules:
  - Mathlib.Dynamics.Ergodic.Conservative
explains:
  E3: [MeasureTheory.Conservative, MeasureTheory.MeasurePreserving.conservative, MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem, MeasureTheory.Conservative.frequently_measure_inter_ne_zero, MeasureTheory.Conservative.ae_frequently_mem_of_mem_nhds, MeasureTheory.Conservative.iterate]
  E2: [MeasureTheory.Conservative.toQuasiMeasurePreserving, MeasureTheory.Conservative.exists_mem_iterate_mem, MeasureTheory.Conservative.exists_gt_measure_inter_ne_zero, MeasureTheory.Conservative.measure_mem_forall_ge_image_notMem_eq_zero, MeasureTheory.Conservative.inter_frequently_image_mem_ae_eq, MeasureTheory.Conservative.measure_inter_frequently_image_mem_eq, MeasureTheory.Conservative.ae_forall_image_mem_imp_frequently_image_mem, MeasureTheory.Conservative.frequently_ae_mem_and_frequently_image_mem, MeasureTheory.Conservative.id, MeasureTheory.Conservative.of_absolutelyContinuous, MeasureTheory.Conservative.measureRestrict, MeasureTheory.Conservative.congr_ae, MeasureTheory.conservative_congr]
  E1: auto
families: []
requires: [V18, V21.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Conservative maps and Poincaré recurrence

### Overview

Section 1 proved that a set of positive measure meets one of its preimages, when the map preserves a finite measure. This section proves the strong form, the recurrence theorem of Poincaré: almost every point of the set returns to it infinitely often. The right hypothesis is weaker than measure preservation. A map is conservative if no set of positive measure can leave itself for ever. The section defines conservative maps, shows that finite measure preserving maps are conservative, and proves recurrence for sets and, on a second countable space, for neighbourhoods.

### Definitions

Let $(X, \mu)$ be a measure space and $f : X \to X$ a measurable map.

**Definition (Wandering set).** A measurable set $W$ is *wandering* if the sets $W, f^{-1}(W), f^{-2}(W), \dots$ are pairwise disjoint.

**Definition (Conservative map).** The map $f$ is *conservative* for $\mu$ if it is quasi measure preserving and each measurable set $s$ with $\mu(s) > 0$ contains a point $x$ with $f^m(x) \in s$ for some $m \ge 1$.

**Lemma (Wandering sets).** A quasi measure preserving map is conservative if and only if every wandering set is null.

*Proof.* Let $W$ be wandering. If $x \in W$ and $f^m(x) \in W$ with $m \ge 1$, then $x \in W \cap f^{-m}(W) = \emptyset$. So no point of $W$ returns, and conservativity forces $\mu(W) = 0$. Conversely, let $s$ be measurable with $\mu(s) > 0$ and no returning point. If $x \in f^{-i}(s) \cap f^{-j}(s)$ with $i < j$, then $y = f^i(x) \in s$ and $f^{j-i}(y) \in s$, which is false. So $s$ is wandering of positive measure. $\square$

::: mathlib
`MeasureTheory.Conservative` · `Mathlib.Dynamics.Ergodic.Conservative`

`Conservative f μ` is a structure with a field `toQuasiMeasurePreserving : QuasiMeasurePreserving f μ μ` and the return property for measurable sets: `∀ ⦃s⦄, MeasurableSet s → μ s ≠ 0 → ∃ x ∈ s, ∃ m, m ≠ 0 ∧ f^[m] x ∈ s`. The lemma `Conservative.exists_mem_iterate_mem` extends the property to null measurable sets. The index of this edition has no declaration for wandering sets.

<?decl MeasureTheory.Conservative?>
:::

### Theorems and proofs

**Theorem (Finite measure preserving maps are conservative).** If $\mu$ is finite and $f$ preserves $\mu$, then $f$ is conservative.

*Proof.* $f$ is quasi measure preserving, and the return property is the corollary of the pigeonhole theorem of Section 1. $\square$

**Theorem (Poincaré recurrence).** Let $f$ be conservative and $s$ measurable. For almost every $x \in s$, there are infinitely many $n$ with $f^n(x) \in s$.

*Proof.* Let $A = \{x \in s : f^m(x) \notin s \text{ for all } m \ge 1\} = s \cap \bigcap_{m \ge 1} f^{-m}(X \setminus s)$, the points of $s$ that never return. It is measurable. If $\mu(A) > 0$, then conservativity gives $x \in A$ and $m \ge 1$ with $f^m(x) \in A \subseteq s$, which contradicts $x \in A$. So $\mu(A) = 0$.

Now let $x \in s$ visit $s$ only finitely often. The set of $k \ge 0$ with $f^k(x) \in s$ contains $0$ and is finite, so it has a largest element $k$. Then $f^k(x) \in s$ and $f^m(f^k(x)) \notin s$ for $m \ge 1$, so $f^k(x) \in A$, that is $x \in f^{-k}(A)$. Each iterate $f^k$ is quasi measure preserving, so $\mu(f^{-k}(A)) = 0$. The set of such $x$ lies in the countable union $\bigcup_{k \ge 0} f^{-k}(A)$, a null set. $\square$

For a null measurable set $s$, choose a measurable $s'$ with $s = s'$ a.e. The sets $f^{-n}(s)$ and $f^{-n}(s')$ agree a.e. by quasi measure preservation, so the statement transfers.

**Corollary (Recurrence of measures).** If $f$ is conservative and $\mu(s) > 0$, then $\mu(s \cap f^{-m}(s)) > 0$ for infinitely many $m$.

*Proof.* Suppose that $\mu(s \cap f^{-m}(s)) = 0$ for all $m > N$. Then the union $Z = \bigcup_{m > N} (s \cap f^{-m}(s))$ is null. Each $x \in s \setminus Z$ visits $s$ at no time $m > N$. By the theorem, almost every $x \in s$ visits $s$ infinitely often, so $\mu(s \setminus Z) = 0$, and $\mu(s) = 0$. $\square$

**Theorem (Recurrence of points).** Let $X$ be a topological space with a countable base, with all open sets measurable, and let $f$ be conservative. For almost every $x$ and every neighbourhood $U$ of $x$, there are infinitely many $n$ with $f^n(x) \in U$.

*Proof.* Let $(V_i)_{i \in \mathbb{N}}$ be a countable base. By Poincaré recurrence, for each $i$ the set $N_i$ of points $x \in V_i$ that visit $V_i$ only finitely often is null. So $N = \bigcup_i N_i$ is null. Let $x \notin N$ and let $U$ be a neighbourhood of $x$. Choose $i$ with $x \in V_i \subseteq U$. Since $x \notin N_i$, $f^n(x) \in V_i \subseteq U$ for infinitely many $n$. $\square$

So almost every point $x$ lies in its own $\omega$-limit set, in the sense of Chapter 2.

**Theorem (Iterates).** If $f$ is conservative, then $f^n$ is conservative for each $n \ge 1$.

*Proof.* The iterate $f^n$ is quasi measure preserving. Let $\mu(s) > 0$ with $s$ measurable. By Poincaré recurrence there is $x \in s$ with $f^k(x) \in s$ for infinitely many $k$. Take $n + 1$ such times $k_0 < \dots < k_n$. Two of them, $k_i < k_j$, have the same residue modulo $n$. Put $y = f^{k_i}(x) \in s$ and $m = (k_j - k_i)/n \ge 1$. Then $(f^n)^m(y) = f^{k_j}(x) \in s$. $\square$

### Examples

**Example (Translation on the line).** The map $x \mapsto x + 1$ preserves Lebesgue measure on $\mathbb{R}$. The set $[0, 1)$ is wandering: its preimages $[-n, 1 - n)$ are disjoint. So the map is not conservative, and recurrence fails. The finiteness hypothesis of the first theorem cannot be dropped.

**Example (Dilation).** The map $x \mapsto 2x$ on $\mathbb{R}$ is quasi measure preserving. The set $W = [1, 2)$ has preimages $f^{-n}(W) = [2^{-n}, 2^{1-n})$, which are disjoint. So $W$ is wandering and the map is not conservative.

**Example (Rotations).** A rotation of the circle preserves the Haar probability measure, so it is conservative. Each orbit of an irrational rotation is dense, and each point returns to each of its neighbourhoods, in agreement with the theorem on points. A rational rotation is periodic, and each point returns exactly.

**Example (Binary words).** Let $D(x) = 2x \bmod 1$ on $[0, 1)$, and let $w$ be a finite binary word of length $\ell$. The set $[w]$ of numbers whose binary expansion starts with $w$ is an interval of length $2^{-\ell}$, and $D^n(x) \in [w]$ means that the digits of $x$ at places $n + 1$ to $n + \ell$ form $w$. By Section 1, $D$ preserves Lebesgue measure. So for almost every $x$ that starts with $w$, the word $w$ appears again infinitely often in the expansion of $x$. Chapter 6 shows the stronger statement that it appears with frequency $2^{-\ell}$.

### The library around it

::: mathlib
`MeasureTheory.MeasurePreserving.conservative` · `Mathlib.Dynamics.Ergodic.Conservative`

`[IsFiniteMeasure μ] → MeasurePreserving f μ μ → Conservative f μ`. Other ways to get a conservative map are `Conservative.id`, `Conservative.iterate`, `Conservative.of_absolutelyContinuous` for a measure $\nu \ll \mu$ with $f$ quasi measure preserving for $\nu$, `Conservative.measureRestrict` for a set with `Set.MapsTo f s s`, and `congr_ae` and `conservative_congr` for measures with the same null sets.

<?decl MeasureTheory.MeasurePreserving.conservative?>
:::

::: mathlib
`MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem` · `Mathlib.Dynamics.Ergodic.Conservative`

`Conservative f μ → NullMeasurableSet s μ → ∀ᵐ x ∂μ, x ∈ s → ∃ᶠ n in atTop, f^[n] x ∈ s`. The step with a fixed $n$ is `measure_mem_forall_ge_image_notMem_eq_zero`. The set forms are `inter_frequently_image_mem_ae_eq` and `measure_inter_frequently_image_mem_eq`. The version `ae_forall_image_mem_imp_frequently_image_mem` starts at any time $k$ with $f^k(x) \in s$, and `frequently_ae_mem_and_frequently_image_mem` says that the set of recurrent points of $s$ is not null.

<?decl MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem?>
:::

::: mathlib
`MeasureTheory.Conservative.frequently_measure_inter_ne_zero` · `Mathlib.Dynamics.Ergodic.Conservative`

`∃ᶠ m in atTop, μ (s ∩ f^[m] ⁻¹' s) ≠ 0`, for `μ s ≠ 0`. The form `exists_gt_measure_inter_ne_zero` gives some `m > N` for each `N`.

<?decl MeasureTheory.Conservative.frequently_measure_inter_ne_zero?>
:::

::: mathlib
`MeasureTheory.Conservative.ae_frequently_mem_of_mem_nhds` · `Mathlib.Dynamics.Ergodic.Conservative`

With `[SecondCountableTopology α]` and `[OpensMeasurableSpace α]`, `∀ᵐ x ∂μ, ∀ s ∈ 𝓝 x, ∃ᶠ n in atTop, f^[n] x ∈ s`. The hypothesis `OpensMeasurableSpace` says that open sets are measurable; the space need not be Borel.

<?decl MeasureTheory.Conservative.ae_frequently_mem_of_mem_nhds?>
:::

Common errors of a learner:

- The recurrence theorem is about almost every point of $s$, not every point. For the doubling map, the point $\tfrac12 \in [\tfrac12, 1)$ goes to the fixed point $0$ and never returns.
- `Conservative` includes quasi measure preservation. A map that has the return property but sends a positive set into a null set is not conservative in Mathlib.
- The frequently filter `∃ᶠ n in atTop` means "for infinitely many $n$", not "for all large $n$".

### Exercises

1. (A) Show that a quasi measure preserving map $f$ with $f^p = \mathrm{id}$ for some $p \ge 1$ is conservative.
2. (A) Let $f$ be conservative and $s$ measurable with $f^{-1}(s) \subseteq s$. Show that $s \setminus f^{-1}(s)$ is null. Hint: it is wandering.
3. (A) Show that $x \mapsto x + 1$ on $\mathbb{Z}$ with counting measure is not conservative, and find a wandering set.
4. (B) Let $f$ be conservative and let $s$ have $\mu(s) > 0$. Show that the first return time $r(x) = \min\{m \ge 1 : f^m(x) \in s\}$ is finite for almost every $x \in s$, and that it is measurable.
5. (B) Let $X$ be compact metric, $f$ continuous, and $\mu$ an invariant probability measure whose support is $X$. Show that the recurrent points of $f$ are dense in $X$.
6. (C) Let $f$ be conservative and $g : X \to [0, \infty]$ measurable with $g \circ f \le g$ a.e. Show that $g \circ f = g$ a.e. Hint: if not, some rational $q$ has $g \circ f \le q < g$ on a set of positive measure; use Exercise 2 for $s = \{g > q\}$, with the inclusion holding a.e.

### Notes and history

Poincaré proved the recurrence theorem in his 1890 memoir on the three body problem, for flows that preserve volume. Carathéodory gave a proof in the language of measure theory in 1919.

### Reference

<?reference?>
