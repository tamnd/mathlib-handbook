---
title: The real numbers
kind: theory
modules:
  - Mathlib.Basic.Real.Basic
  - Mathlib.Algebra.Order.CauSeq.Basic
  - Mathlib.Algebra.Order.CauSeq.Completion
  - Mathlib.Algebra.Order.CauSeq.BigOperators
  - Mathlib.Basic.Real.Sign
  - Mathlib.Basic.Real.Star
  - Mathlib.Data.Real.Basic
  - Mathlib.Data.Real.Sign
  - Mathlib.Data.Real.Star
  - Mathlib.Data.Real.StarOrdered
  - Mathlib.Data.Real.Sqrt
explains:
  E3: [Real, CauSeq]
  E2: [Real.ofCauchy, Real.mk, Real.mk_le, Real.ind_mk, CauSeq.Pos, CauSeq.LimZero, CauSeq.trichotomy, Real.mk_eq]
  E1: auto
families: []
requires: [V02.C04, V02.C05]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V02/C07/Examples.lean
  - MathlibHandbook/V02/C07/Exercises.lean
  - MathlibHandbook/V02/C07/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The real numbers

### Overview

The decimal approximations $1, 1.4, 1.41, \dots$ of $\sqrt 2$ have no rational limit (Chapter 4). Mathlib uses the construction of Cantor: a real number is a class of Cauchy sequences of rational numbers, and two sequences are in the same class when their difference goes to $0$. This section proves that the classes form an ordered field. The next section proves that this field is complete.

### Definitions

A sequence is a function $a : \mathbb{N} \to \mathbb{Q}$, and each $\varepsilon$ or $\delta$ is a positive rational number.

**Definition (Cauchy sequence).** A sequence $a$ is a *Cauchy sequence* if for each $\varepsilon > 0$ there is $N$ with $|a_m - a_n| < \varepsilon$ for all $m, n \geq N$.

::: mathlib
`CauSeq` · `Mathlib.Algebra.Order.CauSeq.Basic`

`CauSeq β abv` is the subtype of the `f : ℕ → β` with `IsCauSeq abv f`, for an absolute value `abv`. The real numbers use `CauSeq ℚ abs`. `IsCauSeq` compares each term with one fixed term $f_i$; the triangle inequality makes this equivalent to the definition above, and `IsCauSeq.cauchy₂` gives the form with two terms.

<?decl CauSeq?>
:::

**Definition (Null and equivalent sequences).** A sequence $a$ is a *null sequence* if for each $\varepsilon > 0$ there is $N$ with $|a_n| < \varepsilon$ for $n \geq N$. Two Cauchy sequences are *equivalent*, $a \approx b$, if $a - b$ is a null sequence.

::: mathlib
`CauSeq.LimZero` · `Mathlib.Algebra.Order.CauSeq.Basic`

`f.LimZero` says that `f` is a null sequence, and `f ≈ g` is `(f - g).LimZero`.

<?decl CauSeq.LimZero?>
:::

**Definition (Positive sequence).** A Cauchy sequence $a$ is *positive* if there are $\delta > 0$ and $N$ with $a_n \geq \delta$ for $n \geq N$.

The sequence $1/(n+1)$ has positive terms, but it is a null sequence and is not positive in this sense.

::: mathlib
`CauSeq.Pos` · `Mathlib.Algebra.Order.CauSeq.Basic`

`f.Pos` is $\exists K > 0, \exists i, \forall j \geq i, K \leq f_j$. On `CauSeq`, `f < g` means `(g - f).Pos`.

<?decl CauSeq.Pos?>
:::

**Definition (The real numbers).** A *real number* is a class $[a]$ of Cauchy sequences for $\approx$. A rational $q$ gives $[q]$, the class of the constant sequence.

::: mathlib
`Real` · `Mathlib.Basic.Real.Basic`

`ℝ` is a structure with one field `Real.cauchy` of type `CauSeq.Completion.Cauchy abs`, the quotient, and the constructor `Real.ofCauchy`. The structure makes `ℝ` a new type, so Lean does not unfold it to the quotient. The operations are irreducible for the same reason.

<?decl Real?>
:::

::: mathlib
`Real.mk` · `Mathlib.Basic.Real.Basic`

`Real.mk f` is the class $[f]$. The lemmas `Real.mk_add`, `Real.mk_mul` and `Real.mk_const` move the operations to the representatives, and `Real.mk_eq` says $[f] = [g] \iff f \approx g$.

<?decl Real.mk?>
:::

### Theorems and proofs

**Lemma (Cauchy sequences are bounded).** For each Cauchy sequence $a$ there is $B$ with $|a_n| \leq B$ for each $n$.

*Proof.* Take $\varepsilon = 1$: there is $N$ with $|a_n - a_N| < 1$ for $n \geq N$, so $|a_n| < |a_N| + 1$ for these $n$. Let $B$ be the largest of $|a_0|, \dots, |a_{N-1}|, |a_N| + 1$. $\square$

**Theorem (Equivalence relation).** The relation $\approx$ is an equivalence relation.

*Proof.* $a - a = 0$ is a null sequence, and $|b_n - a_n| = |a_n - b_n|$ gives symmetry. For transitivity, let $a \approx b$, $b \approx c$ and $\varepsilon > 0$. For $n$ large, $|a_n - b_n| < \varepsilon/2$ and $|b_n - c_n| < \varepsilon/2$, so $|a_n - c_n| < \varepsilon$. $\square$

**Theorem (The product is well defined).** If $a, b$ are Cauchy sequences, $a b$ is a Cauchy sequence. If $a \approx a'$ and $b \approx b'$, then $a b \approx a' b'$.

*Proof.* Let $|a_n| \leq A$ and $|b_n|, |b'_n| \leq B$ with $A, B > 0$, by the lemma. From $a_m b_m - a_n b_n = a_m (b_m - b_n) + b_n (a_m - a_n)$,
$$|a_m b_m - a_n b_n| \leq A |b_m - b_n| + B |a_m - a_n|,$$
and this is $< \varepsilon$ for $m, n$ large. In the same way $|a_n b_n - a'_n b'_n| \leq A |b_n - b'_n| + B |a_n - a'_n|$, which is $< \varepsilon$ for $n$ large. $\square$

The sum and the negation are the same with no bounds. So $[a] + [b] = [a + b]$, $-[a] = [-a]$ and $[a][b] = [a b]$ are well defined, and the ring axioms hold because they hold term by term.

**Lemma (Away from zero).** If a Cauchy sequence $a$ is not a null sequence, there are $\delta > 0$ and $N$ with $a_n \geq \delta$ for all $n \geq N$, or $a_n \leq -\delta$ for all $n \geq N$.

*Proof.* There is $\varepsilon > 0$ such that $|a_n| \geq \varepsilon$ for infinitely many $n$. Choose $N$ with $|a_m - a_n| < \varepsilon/2$ for $m, n \geq N$, and $k \geq N$ with $|a_k| \geq \varepsilon$. Let $\delta = \varepsilon/2$. If $a_k \geq \varepsilon$, then $a_n > a_k - \delta \geq \delta$ for $n \geq N$. If $a_k \leq -\varepsilon$, then $a_n < a_k + \delta \leq -\delta$. $\square$

**Theorem (Trichotomy).** For each Cauchy sequence $a$, exactly one of these holds: $a$ is positive, $a$ is a null sequence, $-a$ is positive.

*Proof.* The lemma gives one case. If $a_n \geq \delta$ for $n \geq N$, then $|a_n| \geq \delta$, so $a$ is not null, and $-a_n < 0$, so $-a$ is not positive. The case of $-a$ is the same. $\square$

::: mathlib
`CauSeq.trichotomy` · `Mathlib.Algebra.Order.CauSeq.Basic`

The statement `f.Pos ∨ f.LimZero ∨ (-f).Pos` does not say that the cases exclude each other.

<?decl CauSeq.trichotomy?>
:::

**Lemma (Sign lemma).** If $a$ is positive and $a' \approx a$, then $a'$ is positive. Sums and products of positive sequences are positive.

*Proof.* Let $a_n \geq \delta$ for $n \geq N$, and choose $M \geq N$ with $|a'_n - a_n| < \delta/2$ for $n \geq M$. Then $a'_n > \delta/2$. If also $b_n \geq \eta$, then $a_n + b_n \geq \delta + \eta$ and $a_n b_n \geq \delta \eta$. $\square$

So $[a] > 0$ is well defined, and $x < y$ means $y - x > 0$.

**Theorem (ℝ is an ordered field).** With these operations and this order, $\mathbb{R}$ is an ordered field, and $q \mapsto [q]$ is an injective map of ordered fields.

*Proof.* By trichotomy applied to $y - x$, exactly one of $x < y$, $x = y$, $y < x$ holds, and the sign lemma gives transitivity, $x + z < y + z$ for $x < y$, and $x y > 0$ for $x, y > 0$. For inverses, let $[a] \neq 0$. The lemma gives $|a_n| \geq \delta$ for $n \geq N$. Let $b_n = 1/a_n$ if $a_n \neq 0$ and $b_n = 0$ otherwise. For $m, n \geq N$, $|b_m - b_n| = |a_n - a_m|/|a_m a_n| \leq |a_n - a_m|/\delta^2$, so $b$ is a Cauchy sequence, and $a_n b_n = 1$ for $n \geq N$, so $[a][b] = 1$. Last, constant sequences add and multiply term by term, and for $p < q$ the constant sequence $q - p$ is positive, so $[p] < [q]$. $\square$

::: mathlib
`Real.mk_le` · `Mathlib.Basic.Real.Basic`

$[f] \leq [g] \iff f \leq g$. The instances `Real.instField` and `Real.instIsStrictOrderedRing` record the theorem, and after them a proof uses the general lemmas.

<?decl Real.mk_le?>
:::

::: mathlib
`Real.ind_mk` · `Mathlib.Basic.Real.Basic`

To prove $C(x)$ for each real $x$, it is enough to prove $C([f])$ for each Cauchy sequence $f$.

<?decl Real.ind_mk?>
:::

### Examples

**Example (Two sequences for one number).** $a_n = 1/(n+1)$ is a null sequence: for $n \geq N > 1/\varepsilon$, $|a_n| < \varepsilon$. So $[a] = 0$.

**Example (A sequence for the square root of 2).** Let $a_0 = 1$ and $a_{n+1} = a_n/2 + 1/a_n$, so $1, 3/2, 17/12, 577/408, \dots$. The identity $a_{n+1}^2 - 2 = (a_n^2 - 2)^2/(4 a_n^2)$ gives $a_n^2 \geq 2$ for $n \geq 1$ and $a_n^2 - 2 \leq 4^{-(2^{n-1})}$. For $m \geq n \geq 1$, $0 \leq a_n - a_m = (a_n^2 - a_m^2)/(a_n + a_m) \leq (a_n^2 - 2)/2$. So $a$ is a Cauchy sequence, $a^2 - 2$ is null, and $s = [a]$ has $s^2 = 2$. No rational $q$ has $[q] = s$.

**Example (Lean).** The field lemmas and the tactics `ring` and `linarith` apply to `ℝ`; the class of a constant sequence is a cast; `Real.mk` keeps sums; each real number has a representative; the cast from `ℚ` keeps the strict order.

<?lean MathlibHandbook/V02/C07/Examples.lean#field?>

<?lean MathlibHandbook/V02/C07/Examples.lean#ring_linarith?>

<?lean MathlibHandbook/V02/C07/Examples.lean#mk_const?>

<?lean MathlibHandbook/V02/C07/Examples.lean#mk_add?>

<?lean MathlibHandbook/V02/C07/Examples.lean#ind_mk?>

<?lean MathlibHandbook/V02/C07/Examples.lean#ratCast_lt?>

### The library around it

`Mathlib.Algebra.Order.CauSeq.Basic` has `IsCauSeq`, `CauSeq`, `CauSeq.LimZero`, `CauSeq.Pos` and the lemmas of this section, such as `CauSeq.bounded`, `CauSeq.mul_equiv_mul` and `CauSeq.abv_pos_of_not_limZero`. `Mathlib.Algebra.Order.CauSeq.Completion` builds the quotient `CauSeq.Completion.Cauchy` and defines `CauSeq.IsComplete` and `CauSeq.lim`. `Mathlib.Basic.Real.Basic` defines `Real` with `Real.mk_eq`, `Real.mk_lt` and `Real.ratCast_lt`.

`Mathlib.Algebra.Order.CauSeq.BigOperators` gives tests for Cauchy sequences of partial sums, for an absolute value `abv` in the sense of `IsAbsoluteValue`. A monotone bounded sequence in an archimedean field is Cauchy: `IsCauSeq.of_mono_bounded` and `IsCauSeq.of_decreasing_bounded`. The comparison test is `IsCauSeq.of_abv_le`: if $\operatorname{abv}(f_m) \leq a_m$ for large $m$ and the partial sums of $a$ are Cauchy, the partial sums of $f$ are Cauchy. `IsCauSeq.of_abv` is the test of absolute convergence. The geometric series $\sum x^n$ with $\operatorname{abv}(x) < 1$ gives `IsCauSeq.geo_series` and `IsCauSeq.geo_series_const`, and `IsCauSeq.series_ratio_test` is the ratio test. The theorem `cauchy_product` treats the Cauchy product $\sum_n \sum_{m \leq n} f_m g_{n-m}$. If the series of $\operatorname{abv}(f_n)$ and the series of $g$ have Cauchy partial sums, the difference between the product of the partial sums and the partial sums of the Cauchy product tends to $0$. The definition of the exponential function uses these tests.

`Mathlib.Basic.Real.Sign` defines `Real.sign r` as $-1$, $0$ or $1$ by the sign of $r$, with the value lemmas `Real.sign_of_pos`, `Real.sign_of_neg` and `Real.sign_zero`. The lemmas `Real.sign_neg`, `Real.sign_inv` and `Real.inv_sign` give its behaviour under negation and inversion, `Real.sign_mul_nonneg` states $0 \leq \operatorname{sign}(r) \cdot r$, and `Real.sign_intCast` compares it with the sign of an integer. `Mathlib.Basic.Real.Star` gives the trivial star structure on `ℝ`, `instStarRingReal` with `instTrivialStarReal`, so `star r = r`. The module `Mathlib.Basic.NNReal.Star` does the same for `ℝ≥0`.

### Exercises

1. (A) Show that $a_n = (-1)^n$ is not a Cauchy sequence. *Hint.* Take $\varepsilon = 1$.
2. (A) Show that a convergent sequence of rational numbers is a Cauchy sequence. *Hint.* Use $|a_m - a_n| \leq |a_m - q| + |q - a_n|$.
3. (B) Show that if $a_n \geq 0$ for each $n$, then $[a] \geq 0$. *Hint.* If $-a$ is positive, $a_n \leq -\delta$ for large $n$.
4. (C) Let $p$ be a prime. Show that $1 + p + \dots + p^n$ is a Cauchy sequence for $|\cdot|_p$, equivalent to the constant $1/(1-p)$. *Hint.* The difference is $-p^{n+1}/(1-p)$.
5. (L) Prove that $(x - y)^2 = x^2 - 2 x y + y^2$ in `ℝ`. The solution is `sub_sq_real`.
6. (L) Prove that each real number is the class of a Cauchy sequence. The solution is `exists_cauSeq_mk`.
7. (L) Prove that `Real.mk` keeps the order. The solution is `mk_le_mk_of_le`.
8. (L) Prove that the cast from `ℚ` to `ℝ` keeps the strict order. The solution is `ratCast_lt_ratCast`.

### Notes and history

Méray (1869), Cantor (1872) and Dedekind (1872, with cuts) gave the first constructions. Mathlib uses Cauchy sequences because the same code gives the $p$ adic numbers. The Lean 3 files are by Mario Carneiro.

### Reference

<?reference?>
