---
title: The real line, its cardinality, its digits and the hyperreals
kind: api
modules:
  - Mathlib.Analysis.Real.Cardinality
  - Mathlib.Analysis.Real.OfDigits
  - Mathlib.Analysis.Real.Hyperreal
  - Mathlib.Analysis.Rat.NatSqrt.Real
explains:
  E2: [Cardinal.cantorFunction_injective, Cardinal.mk_real, Cardinal.mk_Ioo_real, Real.ofDigits_digits, Real.abs_ofDigits_sub_ofDigits_le, Hyperreal.coe_lt_omega, Hyperreal.epsilon_mul_omega, Nat.ratSqrt_mem_Ioc]
  E1: auto
families: []
requires: [V02, V13, V31]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The real line, its cardinality, its digits and the hyperreals

### Overview

The earlier sections use the real numbers as a complete ordered field. This section collects four modules about the set $\mathbb{R}$ itself. The first module proves that $\mathbb{R}$ has the cardinality of the continuum $\mathfrak{c} = 2^{\aleph_0}$, and that every interval with two distinct end points has the same cardinality. The second module defines the expansion of a real number in base $b$ and proves that every number of $[0, 1)$ is the sum of its digit series. The third module builds the hyperreal numbers $\mathbb{R}^*$, an ordered field that contains $\mathbb{R}$ and also infinite and infinitesimal elements. The fourth module bounds a rational approximation of $\sqrt n$.

All four modules use the series and the limits of the earlier sections. The proofs of the first two modules are applications of the geometric series. The hyperreals use an ultrafilter on $\mathbb{N}$ and the germs of sequences along it, from the volume on general topology.

### The library around it

#### The cardinality of the reals

The module `Mathlib.Analysis.Real.Cardinality` writes cardinals with `Cardinal.mk`, with the notation `#α`, and the continuum is `Cardinal.continuum`, with the notation `𝔠`. The key tool is the *Cantor function*. For a real $c$ and a sequence of booleans $f : \mathbb{N} \to \mathrm{Bool}$, `Cardinal.cantorFunctionAux c f n` is $c^n$ when $f(n)$ is true and $0$ otherwise (`Cardinal.cantorFunctionAux_true`, `Cardinal.cantorFunctionAux_false`), and
$$\mathrm{cantorFunction}_c(f) = \sum_{n \ge 0} [f(n)]\, c^n.$$
This is `Cardinal.cantorFunction`. For $0 \le c < 1$ the series converges (`Cardinal.summable_cantor_function`) because it is bounded by the geometric series. `Cardinal.cantorFunction_succ` splits off the first term: the value is $[f(0)] + c \cdot \mathrm{cantorFunction}_c(f(\cdot + 1))$.

**Theorem.** For $0 < c < 1/2$ the map $f \mapsto \mathrm{cantorFunction}_c(f)$ is injective.

*Proof.* Let $f \ne g$ and let $n$ be the first index with $f(n) \ne g(n)$. Say $f(n)$ is false and $g(n)$ is true. The terms with index less than $n$ agree. The terms of $f$ with index greater than $n$ sum to at most $\sum_{k > n} c^k = c^{n+1}/(1 - c)$. Since $c < 1/2$, $c/(1 - c) < 1$, so this sum is less than $c^n$, the term of $g$ at $n$. So $\mathrm{cantorFunction}_c(f) < \mathrm{cantorFunction}_c(g)$. $\square$

The strict inequality of the proof is `Cardinal.increasing_cantorFunction`, and the theorem is `Cardinal.cantorFunction_injective`. With $c = 1/3$ the image is the Cantor set.

**Theorem.** $\#\mathbb{R} = \mathfrak{c}$.

*Proof.* For $\le$: the equivalence `Real.equivCauchy` identifies $\mathbb{R}$ with a quotient of the Cauchy sequences $\mathbb{N} \to \mathbb{Q}$. There are at most $\aleph_0^{\aleph_0} = \mathfrak{c}$ of these sequences. For $\ge$: the Cantor function with $c = 1/3$ is an injection of $\mathbb{N} \to \mathrm{Bool}$ into $\mathbb{R}$, and $2^{\aleph_0} = \mathfrak{c}$ by `Cardinal.two_power_aleph0`. $\square$

This is `Cardinal.mk_real`. Its consequences are `Cardinal.mk_univ_real`, the instance `Cardinal.instUncountableReal` and `Cardinal.not_countable_real`, which use $\aleph_0 < \mathfrak{c}$ (`Cardinal.aleph0_lt_continuum`).

The intervals follow. `Cardinal.mk_Ioi_real` states $\#(a, \infty) = \mathfrak{c}$. The proof is by contradiction: $\mathbb{R} = (-\infty, a) \cup \{a\} \cup (a, \infty)$, and the reflection $x \mapsto 2a - x$ maps $(a, \infty)$ onto $(-\infty, a)$. If $(a, \infty)$ had a smaller cardinality, then the union would be smaller than $\mathfrak{c}$. For a bounded interval the proof of `Cardinal.mk_Ioo_real` is short.

**Theorem.** For $a < b$, $\#(a, b) = \mathfrak{c}$.

*Proof.* The cardinality is at most $\#\mathbb{R} = \mathfrak{c}$. The translation $x \mapsto x - a$ maps $(a, b)$ onto $(0, b - a)$. The inversion $x \mapsto 1/x$ maps $(0, b - a)$ onto $(1/(b - a), \infty)$, which has cardinality $\mathfrak{c}$. An image has at most the cardinality of its source. $\square$

The other seven lemmas `Cardinal.mk_Ici_real`, `Cardinal.mk_Iio_real`, `Cardinal.mk_Iic_real`, `Cardinal.mk_Ico_real`, `Cardinal.mk_Icc_real`, `Cardinal.mk_Ioc_real` and `Cardinal.mk_unitInterval` follow by inclusion. The simp lemmas `Cardinal.Real.Ioo_countable_iff`, `Cardinal.Real.Ico_countable_iff`, `Cardinal.Real.Ioc_countable_iff` and `Cardinal.Real.Icc_countable_iff` state that an interval is countable exactly when it is empty or a point, that is, $y \le x$.

#### Digits in base $b$

The module `Mathlib.Analysis.Real.OfDigits` works with digit sequences `ℕ → Fin b`. For such a sequence $d$, `Real.ofDigitsTerm d i` is $d_i / b^{i+1}$, and
$$\mathrm{ofDigits}(d) = \sum_{i \ge 0} \frac{d_i}{b^{i+1}} = 0.d_0 d_1 d_2 \ldots$$
is `Real.ofDigits`. The terms are nonnegative and at most $(b - 1)/b^{i+1}$ (`Real.ofDigitsTerm_nonneg`, `Real.ofDigitsTerm_le`), so the series converges (`Real.summable_ofDigitsTerm`) and $0 \le \mathrm{ofDigits}(d) \le 1$ (`Real.ofDigits_nonneg`, `Real.ofDigits_le_one`). The value $1$ occurs: `Real.ofDigits_const_last_eq_one` states $0.(b-1)(b-1)\ldots = 1$, the identity $0.999\ldots = 1$ in base $10$. So the map from digit sequences to $[0, 1]$ is surjective (`Real.ofDigits_SurjOn`) but not injective. `Real.ofDigits_eq_sum_add_ofDigits` splits off the first $n$ digits: $\mathrm{ofDigits}(d) = \sum_{i < n} d_i / b^{i+1} + b^{-n} \mathrm{ofDigits}(d_{\cdot + n})$.

**Theorem.** If two digit sequences agree in the first $n$ places, then their values differ by at most $b^{-n}$.

*Proof.* By the splitting lemma the two values have the same first part. The two tails are $b^{-n}$ times numbers of $[0, 1]$, so they differ by at most $b^{-n}$. $\square$

This is `Real.abs_ofDigits_sub_ofDigits_le`. It gives `Real.continuous_ofDigits` for the product topology on the digit sequences.

In the other direction, `Real.digits x b` is the sequence of the digits of $x$: the digit $d_i$ is $\lfloor x b^{i+1} \rfloor$ modulo $b$. The partial sums of the digit series satisfy $b^n \sum_{i < n} d_i / b^{i+1} = \lfloor b^n x \rfloor$ for $x \in [0, 1)$ (`Real.ofDigits_digits_sum_eq`). So the partial sum is the truncation of $x$ to $n$ places, and it lies in $[x - b^{-n}, x]$ (`Real.le_sum_ofDigitsTerm_digits`, `Real.sum_ofDigitsTerm_digits_le`). As $n \to \infty$ the partial sums tend to $x$.

**Theorem.** For $b > 1$ and $x \in [0, 1)$, $\mathrm{ofDigits}(\mathrm{digits}(x, b)) = x$.

This is `Real.ofDigits_digits`, with the series form `Real.hasSum_ofDigitsTerm_digits`. The function `Real.digits` chooses the expansion that does not end in a constant tail of $b - 1$, because the floor rounds down.

#### The hyperreal numbers

The module `Mathlib.Analysis.Real.Hyperreal` defines `Hyperreal`, with the notation `ℝ*`, as the type of germs of real sequences along the ultrafilter `Filter.hyperfilter ℕ`. This ultrafilter contains the cofinite filter. Two sequences give the same hyperreal when they agree on a set of the ultrafilter. The function `Hyperreal.ofSeq` sends a sequence to its class, and it is surjective (`Hyperreal.ofSeq_surjective`). The order and the field operations come from the germs: the instances `Hyperreal.instField`, `Hyperreal.instLinearOrder` and `Hyperreal.instIsStrictOrderedRing` make `ℝ*` a linearly ordered field. The order compares two sequences on a set of the ultrafilter (`Hyperreal.ofSeq_le_ofSeq`, `Hyperreal.ofSeq_lt_ofSeq`). The order is linear because an ultrafilter contains each set or its complement.

A real number $r$ is the class of the constant sequence. The coercion is `Hyperreal.ofReal`, and `Hyperreal.coeRingHom` is the same map as an ordered ring homomorphism. The `coe_` lemmas move the coercion through the operations: `Hyperreal.coe_add`, `Hyperreal.coe_mul`, `Hyperreal.coe_inv`, `Hyperreal.coe_abs`, `Hyperreal.coe_max` and the order lemmas `Hyperreal.coe_le_coe`, `Hyperreal.coe_lt_coe`. The simp normal form has the coercion outside: `↑(x + y)` becomes `↑x + ↑y`.

The two sample elements are `Hyperreal.omega`, written `ω`, the class of $(0, 1, 2, \ldots)$, and `Hyperreal.epsilon`, written `ε`, the class of $(0, 1, 1/2, 1/3, \ldots)$. The notations are scoped in the namespace `Hyperreal`.

**Theorem.** $r < \omega$ for every real $r$.

*Proof.* Choose a natural number $n > r$. Then $r < m$ for all $m \ge n$. The set $\{m : m \ge n\}$ is cofinite, so it is in the ultrafilter. So the constant sequence $r$ is less than the sequence $(m)$ on a set of the ultrafilter. $\square$

This is `Hyperreal.coe_lt_omega`. So `ℝ*` is not Archimedean. The relation $\varepsilon \omega = 1$ (`Hyperreal.epsilon_mul_omega`) holds because $m \cdot m^{-1} = 1$ for all $m \ne 0$, a cofinite set. The simp lemmas `Hyperreal.inv_omega` and `Hyperreal.inv_epsilon` state $\omega^{-1} = \varepsilon$ and $\varepsilon^{-1} = \omega$. With `Hyperreal.epsilon_pos` and `Hyperreal.epsilon_lt_of_pos`, $\varepsilon$ is positive and less than every positive real: it is an infinitesimal.

Mathlib does not define "infinitesimal", "infinite" and "standard part" for `ℝ*` alone. It uses general notions for ordered fields. `ArchimedeanClass.mk x` is the Archimedean class of $x$: a class less than $0$ means that $x$ is infinite (`Hyperreal.archimedeanClassMk_omega_neg`), and a class greater than $0$ means that $x$ is infinitesimal (`Hyperreal.archimedeanClassMk_epsilon_pos`). A nonzero real has class $0$ (`Hyperreal.archimedeanClassMk_coe`). `ArchimedeanClass.stdPart x` is the standard part: for a finite $x$ it is the unique real number $r$ with $x - r$ infinitesimal, and for an infinite $x$ it is $0$. Then `Hyperreal.stdPart_coe` gives $\mathrm{st}(r) = r$, and `Hyperreal.stdPart_omega` and `Hyperreal.stdPart_epsilon` give $0$.

The link to limits uses `Filter.Germ.Tendsto`. A hyperreal $x$ tends to $r$ when its sequences tend to $r$ along the ultrafilter. `Hyperreal.tendsto_iff_forall` states that this holds exactly when $s \le x$ for every real $s < r$ and $x \le s$ for every real $s > r$. Then `Hyperreal.stdPart_of_tendsto` gives $\mathrm{st}(x) = r$. The lemmas `Hyperreal.stdPart_map` and `Hyperreal.stdPart_map₂` state that a function continuous at $r$ commutes with this limit. `Hyperreal.tendsto_atTop_iff` characterizes the positive infinite elements: positive and of negative class.

#### Rational square roots

The function `Nat.ratSqrt x prec` of `Mathlib.Data.Rat.NatSqrt.Defs` is the rational number $\lfloor\sqrt{x\,p^2}\rfloor / p$ for the precision $p$. The module `Mathlib.Analysis.Rat.NatSqrt.Real` compares it with the real square root.

**Theorem.** For $p > 0$, $\sqrt x - 1/p < \mathrm{ratSqrt}(x, p) \le \sqrt x$.

*Proof.* Let $q = \lfloor \sqrt{x p^2} \rfloor = \lfloor p \sqrt x \rfloor$. Then $q \le p \sqrt x < q + 1$. Divide by $p$. $\square$

This is `Nat.ratSqrt_mem_Ioc`. The two halves are `Nat.ratSqrt_le_realSqrt` and `Nat.realSqrt_lt_ratSqrt_add_inv_prec`, and `Nat.realSqrt_mem_Ico` is the same statement seen from $\sqrt x$.

#### Common errors

1. Expecting `Real.ofDigits` to be injective. The sequences $1, 0, 0, \ldots$ and $0, 9, 9, \ldots$ in base $10$ have the same value $1/10$. Only `Real.ofDigits_digits` holds, not the converse composition.
2. Using `ω` or `ε` without opening the namespace. The notations are scoped: write `open Hyperreal` or the full names `Hyperreal.omega` and `Hyperreal.epsilon`.
3. Expecting `ArchimedeanClass.stdPart` to be undefined on an infinite element. It is a total function to `ℝ`, and its value on an infinite element is the junk value $0$. So $\mathrm{st}(\omega) = 0$ does not mean that $\omega$ is near $0$.

### Exercises

1. (A) Show that the set of irrational numbers in $(0, 1)$ has cardinality $\mathfrak{c}$. Hint: `Cardinal.mk_Ioo_real` and the countability of $\mathbb{Q}$.
2. (A) Compute the first five digits of $1/7$ in base $10$ with the formula $d_i = \lfloor x b^{i+1} \rfloor \bmod b$, and check `Real.ofDigits_digits_sum_eq` for $n = 3$.
3. (B) Show that the Cantor function with $c = 1/2$ is not injective, and find two sequences with the same value.
4. (B) Show that $\omega^2 > r \omega$ for every real $r$, and that $\varepsilon^2$ is infinitesimal compared with $\varepsilon$.
5. (B) Let $x = \mathrm{ofSeq}(f)$. Show that if $f(n) \to r$ in the usual sense, then $\mathrm{st}(x) = r$.
6. (C) Show that every interval $(a, b)$ with $a < b$ contains $\mathfrak{c}$ transcendental numbers, with the countability of the algebraic numbers.

### Reference

<?reference?>
