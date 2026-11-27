---
title: Regular, singular and inaccessible cardinals
kind: theory
modules:
  - Mathlib.SetTheory.Cardinal.Regular
  - Mathlib.SetTheory.Cardinal.Pigeonhole
explains:
  E3: [Cardinal.IsRegular, Cardinal.isRegular_succ, Cardinal.IsSingular, Cardinal.IsInaccessible, Cardinal.infinite_pigeonhole]
  E2: [Cardinal.IsRegular.cof_ord, Cardinal.isRegular_aleph0, Cardinal.isRegular_aleph_one, Cardinal.cof_omega_one, Cardinal.isRegular_aleph_add_one, Cardinal.isRegular_cof, Cardinal.sum_lt_of_isRegular, Cardinal.isRegular_or_isSingular, Cardinal.isSingular_aleph_iff, Cardinal.isSingular_aleph_omega0, Cardinal.IsSingular.aleph_omega0_le, Cardinal.isInaccessible_def, Cardinal.IsInaccessible.univ, Cardinal.IsInaccessible.aleph_ord, Cardinal.nfp_lt_ord_of_isRegular, Cardinal.infinite_pigeonhole_card, Cardinal.infinite_pigeonhole_card_lt, Cardinal.exists_infinite_fiber]
  E1: auto
families: []
requires: [V31.C01, V31.C04, V31.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Regular, singular and inaccessible cardinals

### Overview

Section 1 showed that $\operatorname{cf} \kappa \le \kappa$ for each cardinal $\kappa$, where $\operatorname{cf} \kappa$ means the cofinality of the initial ordinal $\kappa.\mathrm{ord}$. This section studies the two cases. An infinite cardinal is *regular* when $\operatorname{cf} \kappa = \kappa$, and *singular* when $\operatorname{cf} \kappa < \kappa$. A regular cardinal cannot be reached from below in fewer than $\kappa$ steps. Equivalently, a union of fewer than $\kappa$ sets, each of size less than $\kappa$, has size less than $\kappa$.

The main results are these. The cardinal $\aleph_0$ is regular. Each successor cardinal $\kappa^+$ is regular, and the proof uses the axiom of choice. The cardinal $\aleph_\omega$ is singular, and it is the least singular cardinal. The regular cardinals are exactly the cardinals for which the infinite pigeonhole principle holds in its strongest form. The section ends with the inaccessible cardinals. ZFC cannot prove that they exist, but the universes of Lean give one at once.

### Definitions

**Definition (Regular cardinal).** A cardinal $\kappa$ is *regular* if $\aleph_0 \le \kappa$ and $\kappa \le \operatorname{cf} \kappa$.

Section 1 gives $\operatorname{cf} \kappa \le \kappa$, so a regular cardinal satisfies $\operatorname{cf} \kappa = \kappa$. Mathlib states the definition with the inequality, because the inequality is the part that a proof must give.

**Definition (Singular cardinal).** A cardinal $\kappa$ is *singular* if $\aleph_0 \le \kappa$ and $\operatorname{cf} \kappa \ne \kappa$.

Each infinite cardinal is regular or singular, and not both. The finite cardinals are neither. The condition $\aleph_0 \le \kappa$ removes the finite cardinals on purpose: with the definitions of Section 1, $\operatorname{cf} 0 = 0$, and $\operatorname{cf} n = 1$ for $n \ge 1$, so the cardinals 0 and 1 would be "regular" without it.

**Definition (Strong limit).** A cardinal $\kappa$ is a *strong limit* if $\kappa \ne 0$ and $2^\mu < \kappa$ for each $\mu < \kappa$.

Chapter 1 introduced this definition. The cardinal $\aleph_0$ is a strong limit, because $2^n$ is finite for $n$ finite. The beth numbers of Chapter 5 give more examples: $\beth_\omega$ is a strong limit.

**Definition (Inaccessible cardinal).** A cardinal $\kappa$ is *inaccessible* if $\aleph_0 < \kappa$, $\kappa$ is regular, and $\kappa$ is a strong limit.

Some books call these cardinals *strongly inaccessible*, and call a regular uncountable limit cardinal *weakly inaccessible*. Mathlib has a structure only for the strong notion.

### Theorems and proofs

**Proposition (Union form of regularity).** Let $\kappa$ be an infinite cardinal. Then $\kappa$ is regular if and only if for each family $(\mu_i)_{i \in I}$ of cardinals with $|I| < \kappa$ and $\mu_i < \kappa$ for each $i$, the sum $\sum_i \mu_i$ is less than $\kappa$.

*Proof.* Assume that $\kappa$ is regular, and let $(\mu_i)$ be such a family. Let $o_i = \mu_i.\mathrm{ord}$. Each $o_i$ is below $\kappa.\mathrm{ord}$, and $|I| < \kappa = \operatorname{cf} \kappa$. The theorem on small suprema of Section 1 gives $\sup_i o_i < \kappa.\mathrm{ord}$, so $\nu = \sup_i \mu_i < \kappa$. Then $$\sum_i \mu_i \le |I| \cdot \nu \le \max(|I|, \nu, \aleph_0) < \kappa,$$ by the theorem $\lambda \cdot \lambda = \lambda$ of Chapter 5 and because $\kappa$ is infinite.

Conversely, assume that $\kappa$ is singular. Let $\lambda = \operatorname{cf} \kappa < \kappa$. Take a cofinal subset $S$ of $[0, \kappa.\mathrm{ord})$ with $|S| = \lambda$. Each $x \in S$ is an ordinal below the initial ordinal $\kappa.\mathrm{ord}$, so $|x| < \kappa$. The sets $[0, x)$ for $x \in S$ cover $[0, \kappa.\mathrm{ord})$, because this ordinal is a limit. So $\kappa \le \sum_{x \in S} |x|$, a sum of $\lambda < \kappa$ cardinals each below $\kappa$. $\square$

In words: for a regular $\kappa$, a union of fewer than $\kappa$ sets, each of size less than $\kappa$, has size less than $\kappa$. For a singular $\kappa$, some such union has size $\kappa$.

**Theorem.** The cardinal $\aleph_0$ is regular.

*Proof.* A finite union of finite sets is finite. By the proposition, this is the claim. $\square$

**Theorem (Successor cardinals are regular).** Let $\kappa$ be an infinite cardinal. Then the successor cardinal $\kappa^+$ is regular.

*Proof.* The proposition applies. Let $(A_i)_{i \in I}$ be sets with $|I| < \kappa^+$ and $|A_i| < \kappa^+$ for each $i$. Then $|I| \le \kappa$ and $|A_i| \le \kappa$, because no cardinal lies strictly between $\kappa$ and $\kappa^+$. So $$\left|\bigcup_i A_i\right| \le \sum_i |A_i| \le \kappa \cdot \kappa = \kappa < \kappa^+.$$ $\square$

The proof is short, but it hides the axiom of choice twice. The bound $|\bigcup_i A_i| \le \sum_i |A_i|$ needs a choice of an injection $A_i \to \kappa$ for each $i$ at the same time, and the comparison of the cardinals $|A_i|$ with $\kappa$ needs the well-ordering theorem. Without choice, it is consistent that $\aleph_1$ is singular, with cofinality $\aleph_0$. In Lean, `Classical.choice` is an axiom (V01, Chapter 1), so the question does not arise in Mathlib.

**Corollary.** For each ordinal $o$, the cardinal $\aleph_{o + 1}$ is regular. In particular, $\aleph_1$ is regular, $\operatorname{cf} \omega_1 = \aleph_1$, and a countable family of countable ordinals has a countable supremum.

*Proof.* $\aleph_{o+1} = \aleph_o^+$ by Chapter 5. For the last claim, let $(\alpha_n)$ be countable ordinals. They are below $\omega_1$, and the family has fewer than $\aleph_1 = \operatorname{cf} \omega_1$ members, so the theorem on small suprema of Section 1 gives $\sup_n \alpha_n < \omega_1$. $\square$

The last claim is used often in analysis. For example, the Borel hierarchy of a metric space stops at the stage $\omega_1$ for this reason.

**Theorem (Cofinalities are regular).** Let $o$ be a limit ordinal. Then $\operatorname{cf} o$ is a regular cardinal.

*Proof.* Section 1 gives $\operatorname{cf} o \ge \aleph_0$ and $\operatorname{cf}((\operatorname{cf} o).\mathrm{ord}) = \operatorname{cf} o$. These are the two conditions. $\square$

So each limit ordinal has a regular cofinality, and the regular cardinals are exactly the values of the cofinality on limit ordinals.

**Theorem (Singular cardinals).** Let $o$ be an ordinal. Then $\aleph_o$ is singular if and only if $o$ is a limit ordinal and $\operatorname{cf} o < \aleph_o$. In particular, $\aleph_\omega$ is singular, and each singular cardinal is at least $\aleph_\omega$.

*Proof.* If $o = 0$, then $\aleph_0$ is regular. If $o$ is a successor, $\aleph_o$ is regular by the corollary. If $o$ is a limit, the map $\beta \mapsto \omega_\beta$ is normal by Chapter 5, and part 3 of the theorem on ordinals of Section 1 gives $\operatorname{cf} \omega_o = \operatorname{cf} o$. So $\aleph_o$ is singular exactly when $\operatorname{cf} o < \aleph_o$.

For $o = \omega$, $\operatorname{cf} \omega = \aleph_0 < \aleph_\omega$. For the last claim, a singular cardinal is infinite, so it is $\aleph_o$ for some $o$ by Chapter 5. The ordinal $o$ is a limit and not 0, so $o \ge \omega$, and $\aleph_o \ge \aleph_\omega$. $\square$

For a limit ordinal $o$, the condition $\operatorname{cf} o < \aleph_o$ is almost always true. It fails only when $o = \aleph_o$ as well as $o$ being regular, that is, when $\aleph_o$ is a regular limit cardinal. That is the definition of a weakly inaccessible cardinal. So above $\aleph_0$, the regular cardinals are the successor cardinals and the weakly inaccessible cardinals.

**Theorem (Infinite pigeonhole principle).** Let $f : B \to A$ be a function, with $B$ infinite and $|A| < \operatorname{cf} |B|$. Then some fiber $f^{-1}(a)$ has the cardinality $|B|$.

*Proof.* Let $\kappa = |B|$. Assume that each fiber has cardinality less than $\kappa$. The fibers cover $B$, so $$\kappa \le \sum_{a \in A} |f^{-1}(a)| \le |A| \cdot \sup_{a \in A} |f^{-1}(a)|.$$ Each fiber has an initial ordinal below $\kappa.\mathrm{ord}$, and $|A| < \operatorname{cf} \kappa$, so the theorem on small suprema of Section 1 gives $\nu = \sup_a |f^{-1}(a)| < \kappa$. Also $|A| < \operatorname{cf} \kappa \le \kappa$. A product of two cardinals below the infinite cardinal $\kappa$ is below $\kappa$ (Chapter 5). This is a contradiction. So some fiber has cardinality at least $\kappa$, and so exactly $\kappa$. $\square$

When $\kappa$ is regular, the hypothesis is only $|A| < \kappa$. When $\kappa$ is singular, the hypothesis on $\operatorname{cf}$ is necessary, as the next example shows.

**Corollary.** Let $f : B \to A$ with $B$ infinite and $|A| < |B|$. Then some fiber of $f$ has cardinality greater than $|A|$. In particular, some fiber is infinite.

*Proof.* If $A$ is finite, apply the theorem with the regular cardinal $\aleph_0$ in place of $|B|$, to a countable subset of $B$. Otherwise, let $\theta = |A|^+$. Then $\theta \le |B|$, and $\theta$ is regular, so $|A| < \theta = \operatorname{cf} \theta$. Apply the theorem to $f$ restricted to a subset of $B$ of cardinality $\theta$. $\square$

**Theorem (Inaccessible cardinals and the alephs).** Let $\kappa$ be inaccessible. Then $\aleph_{\kappa.\mathrm{ord}} = \kappa$ and $\beth_{\kappa.\mathrm{ord}} = \kappa$. So $\kappa$ is a fixed point of the aleph and the beth functions.

*Proof.* The proof for the alephs follows. Write $\kappa = \aleph_o$, so $o \le \aleph_o$ and $o \le \kappa.\mathrm{ord}$. The claim is $o = \kappa.\mathrm{ord}$. Assume that $o < \kappa.\mathrm{ord}$. The ordinal $o$ is a limit, because $\kappa$ is a strong limit and so not a successor cardinal. As in the theorem on singular cardinals, $\operatorname{cf} \kappa = \operatorname{cf} o \le |o| < \kappa$, and $\kappa$ is singular. This is a contradiction. The proof for the beths is the same, with the fact that $\beth_{\beta + 1} = 2^{\beth_\beta}$ is below $\kappa$ for $\beth_\beta < \kappa$. $\square$

**Theorem (A universe gives an inaccessible cardinal).** Let $\mathrm{univ}_u$ be the cardinal of the type `Cardinal.{u}`, read in the universe $u + 1$. Then $\mathrm{univ}_u$ is inaccessible.

*Proof sketch.* Each cardinal $\mu$ of the universe $u$ is a type of `Type u`, and its power set is again in `Type u`. So $2^\mu$ is in the universe $u$, and its lift is below $\mathrm{univ}_u$. This gives the strong limit property. For regularity, a family of fewer than $\mathrm{univ}_u$ cardinals of the universe $u$ is indexed by a type that is equivalent to a type of `Type u`. Its sum is a type of `Type u`, so it is below $\mathrm{univ}_u$. $\square$

This theorem shows that the type theory of Lean is stronger than ZFC. ZFC does not prove that an inaccessible cardinal exists, because the sets of rank below an inaccessible $\kappa$ form a model of ZFC, and so the existence would prove the consistency of ZFC. Chapter 7 returns to this point.

### Examples

**Example (A singular pigeonhole).** Let $B = \bigsqcup_{n} \omega_n$, the disjoint union of the sets $\omega_n$ for $n \in \mathbb{N}$, so $|B| = \aleph_\omega$. Let $f : B \to \mathbb{N}$ send $\omega_n$ to $n$. Each fiber has cardinality $\aleph_n < \aleph_\omega$. So no fiber has the cardinality $|B|$, although $|\mathbb{N}| = \aleph_0 < \aleph_\omega$. The theorem does not apply, because $|\mathbb{N}| = \operatorname{cf} \aleph_\omega$.

**Example (Countable suprema).** Let $(\alpha_n)$ be countable ordinals. The corollary on $\aleph_1$ gives $\sup_n \alpha_n < \omega_1$. For example, the ordinals $\omega, \omega^\omega, \omega^{\omega^\omega}, \dots$ are countable, so their supremum $\varepsilon_0$ is countable, as Chapter 4 found by a direct count.

**Example (Fixed points below a regular cardinal).** Let $\kappa$ be an uncountable regular cardinal and let $f$ be a normal function with $f(\alpha) < \kappa.\mathrm{ord}$ for each $\alpha < \kappa.\mathrm{ord}$. The least fixed point above $\alpha$ is $\sup_n f^n(\alpha)$, from Chapter 4. This supremum is of countably many ordinals below $\kappa.\mathrm{ord}$, and $\aleph_0 < \operatorname{cf} \kappa$, so it is below $\kappa.\mathrm{ord}$. So $f$ has fixed points below $\kappa.\mathrm{ord}$ above each $\alpha$. For $\kappa = \aleph_1$ and $f(\alpha) = \omega^\alpha$, this gives the countable $\varepsilon$ numbers.

**Counterexample ($\aleph_0$ is not enough).** The argument of the last example fails for $\kappa = \aleph_0$. The function $f(\alpha) = 1 + \alpha$ is normal, and $f(n) = n + 1 < \omega$ for each natural number $n$. But the least fixed point of $f$ is $\sup_n f^n(0) = \omega$, because $1 + \omega = \omega$. So $f$ has no fixed point below $\omega$. The supremum of countably many ordinals below $\omega$ need not be below $\omega$, because $\operatorname{cf} \omega = \aleph_0$ is not greater than $\aleph_0$. For this reason, the Mathlib lemma for fixed points takes the hypothesis $\kappa \ne \aleph_0$.

### The library around it

::: mathlib
`Cardinal.IsRegular` · `Mathlib.SetTheory.Cardinal.Regular`

`IsRegular c` is a structure with the fields `aleph0_le : ℵ₀ ≤ c` and `le_cof_ord : c ≤ c.ord.cof`. The equality is `IsRegular.cof_ord : c.ord.cof = c`. The basic instances are `isRegular_aleph0`, `isRegular_aleph_one`, `isRegular_aleph_add_one o`, and `isRegular_cof (h : IsSuccLimit o) : IsRegular o.cof`. The value `cof_omega_one : cof ω₁ = ℵ₁` and `Ordinal.iSup_lt_omega_one` give the countable suprema.

<?decl Cardinal.IsRegular?>
:::

::: mathlib
`Cardinal.isRegular_succ` · `Mathlib.SetTheory.Cardinal.Regular`

`isRegular_succ (hc : ℵ₀ ≤ c) : IsRegular (succ c)`. The proof in Mathlib takes a fundamental sequence of $(\kappa^+).\mathrm{ord}$ and bounds the cardinality of its supremum. It is the same argument as above, in the language of suprema. The sum form of regularity is `sum_lt_of_isRegular (hc : IsRegular c) (hι : #ι < c) : (∀ i, f i < c) → sum f < c`.

<?decl Cardinal.isRegular_succ?>
:::

<?decl Cardinal.sum_lt_of_isRegular?>

::: mathlib
`Cardinal.IsSingular` · `Mathlib.SetTheory.Cardinal.Regular`

`IsSingular c` has the fields `aleph0_le` and `cof_ord_ne : c.ord.cof ≠ c`. The dichotomy is `isRegular_or_isSingular (h : ℵ₀ ≤ c)`. The characterization is `isSingular_aleph_iff : (ℵ_ o).IsSingular ↔ IsSuccLimit o ∧ o.cof < ℵ_ o`, and `isSingular_aleph_omega0` and `IsSingular.aleph_omega0_le` give the least singular cardinal.

<?decl Cardinal.IsSingular?>
:::

::: mathlib
`Cardinal.IsInaccessible` · `Mathlib.SetTheory.Cardinal.Regular`

`IsInaccessible c` has the fields `aleph0_lt`, `le_cof_ord` and `isStrongPrelimit`, and `isInaccessible_def : IsInaccessible c ↔ ℵ₀ < c ∧ IsRegular c ∧ IsStrongLimit c` gives the form of the text. `IsInaccessible.univ : IsInaccessible univ.{u, v}` is the theorem on universes. The fixed points are `IsInaccessible.aleph_ord` and `IsInaccessible.beth_ord`.

<?decl Cardinal.IsInaccessible?>
:::

<?decl Cardinal.IsInaccessible.univ?>

::: mathlib
`Cardinal.infinite_pigeonhole` · `Mathlib.SetTheory.Cardinal.Pigeonhole`

`infinite_pigeonhole (f : β → α) (h₁ : ℵ₀ ≤ #β) (h₂ : #α < (#β).ord.cof) : ∃ a, #(f ⁻¹' {a}) = #β`. The variants are `infinite_pigeonhole_card`, for a cardinal `θ ≤ #β` in place of `#β`, `infinite_pigeonhole_card_lt`, which is the corollary, and `exists_infinite_fiber`, which needs only `#α < #β` and `[Infinite β]`.

<?decl Cardinal.infinite_pigeonhole?>
:::

<?decl Cardinal.exists_infinite_fiber?>

Common errors:

- `IsRegular` is a structure, not a definition by an equality. To prove it, give the two fields, for example with `⟨h₀, h⟩`. To use it, apply `IsRegular.cof_ord`.
- In the lemmas of the pigeonhole principle, `α` and `β` are in the same universe `u`. For types in different universes, lift the cardinals first.
- `nfp_lt_ord_of_isRegular` and `deriv_lt_ord` need the hypothesis `c ≠ ℵ₀`. The countable case is false for most normal functions.
- `Cardinal.univ.{u, v}` is the cardinal of `Ordinal.{u}`, lifted to the universe `max (u + 1) v`. It is not the cardinal of a type of `Type u`, and no such cardinal is inaccessible in the sense of that universe.

### Exercises

1. (A) Show that $\aleph_5$, $\aleph_{\omega + 1}$ and $\aleph_{\omega_1 + 1}$ are regular, and that $\aleph_{\omega + \omega}$ and $\aleph_{\omega_1 + \omega}$ are singular.
2. (A) Let $A \subseteq \omega_1$ be a countable set. Show that $A$ is bounded in $\omega_1$.
3. (A) Show that an uncountable set of real numbers has an element that is a limit point of the set. Hint: the rational intervals are countable.
4. (B) Show that $\aleph_{\omega_1}$ is singular, with cofinality $\aleph_1$. Find a limit ordinal $o > \omega$ for which $\operatorname{cf} \aleph_o = \aleph_0$, and one for which $\operatorname{cf} \aleph_o = \aleph_2$.
5. (B) Let $\kappa$ be regular and uncountable, and let $f : \kappa.\mathrm{ord} \to \kappa.\mathrm{ord}$ be any function. Show that the set of $\alpha < \kappa.\mathrm{ord}$ with $f(\beta) < \alpha$ for each $\beta < \alpha$ is unbounded in $\kappa.\mathrm{ord}$.
6. (B) Show that a weakly inaccessible cardinal $\kappa$ satisfies $\kappa = \aleph_\kappa$. Show that $\aleph_\kappa = \kappa$ does not imply that $\kappa$ is regular, with the least fixed point of $o \mapsto \aleph_o$.
7. (C) Assume the generalized continuum hypothesis, $2^\mu = \mu^+$ for each infinite $\mu$. Show that each weakly inaccessible cardinal is inaccessible.
8. (L) In Lean, prove `Cardinal.IsRegular (Order.succ Cardinal.aleph0)` from `Cardinal.isRegular_succ`, and then use `Cardinal.exists_infinite_fiber` to show that a map from `ℝ` to `ℕ` has an infinite fiber.

### Notes and history

Hausdorff defined the regular cardinals and asked whether a regular limit cardinal above $\aleph_0$ can exist. Sierpiński and Tarski, and independently Zermelo, studied the strongly inaccessible cardinals around 1930. Zermelo used them to describe the models of set theory, and the remark that an inaccessible cardinal gives a model of ZFC comes from that work.

### Reference

<?reference?>
