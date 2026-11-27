---
title: Exponentiation and logarithm
kind: theory
modules:
  - Mathlib.SetTheory.Ordinal.Exponential
  - Mathlib.SetTheory.Ordinal.Commute
explains:
  E3: [Ordinal.instPow, Ordinal.isNormal_opow, Ordinal.log, Ordinal.addCommute_iff_eq_mul_natCast]
  E2: [Ordinal.zero_opow', Ordinal.opow_zero, Ordinal.opow_add_one, Ordinal.opow_limit, Ordinal.opow_pos, Ordinal.opow_add, Ordinal.opow_mul, Ordinal.opow_le_opow_left, Ordinal.opow_lt_opow_iff_right, Ordinal.right_le_opow, Ordinal.opow_natCast, Ordinal.iSup_pow_natCast, Ordinal.opow_le_iff_le_log, Ordinal.lt_opow_iff_log_lt, Ordinal.log_of_left_le_one, Ordinal.log_zero_right, Ordinal.opow_log_le_self, Ordinal.lt_opow_succ_log_self, Ordinal.div_opow_log_lt, Ordinal.mod_opow_log_lt_self, Ordinal.log_opow, Ordinal.log_opow_mul_add]
  E1: auto
families: []
requires: [V04.C01, V04.C02, V31.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Exponentiation and logarithm

### Overview

Exponentiation is defined by recursion: $\alpha^{\beta + 1} = \alpha^\beta \cdot \alpha$, with the supremum at limits. For $\alpha > 1$ the map $\beta \mapsto \alpha^\beta$ is normal, and $\alpha^{\beta + \gamma} = \alpha^\beta \alpha^\gamma$ and $\alpha^{\beta\gamma} = (\alpha^\beta)^\gamma$ hold, but $(\alpha\beta)^\gamma = \alpha^\gamma \beta^\gamma$ fails. Ordinal powers are not cardinal powers: here $2^\omega = \omega$. The logarithm $\log_b x$ is the largest $c$ with $b^c \le x$, and each $x \neq 0$ is $b^c q + r$ with $0 < q < b$ and $r < b^c$. Section 3 repeats this step to get the Cantor normal form. The section ends with the ordinals that commute for addition.

### Definitions

**Definition (Ordinal exponentiation).** For $\alpha \neq 0$, define $\alpha^\beta$ by transfinite recursion on $\beta$:
$$\alpha^0 = 1, \qquad \alpha^{\beta + 1} = \alpha^\beta \cdot \alpha, \qquad \alpha^\lambda = \sup_{\beta < \lambda} \alpha^\beta \text{ for a limit } \lambda.$$
For the base $0$, set $0^0 = 1$ and $0^\beta = 0$ for $\beta \ge 1$.

For the base $0$ the limit clause would give $0^\omega = \sup_n 0^n = 1$. The usual convention, also in Jech, is $0^\beta = 0$ for all $\beta \ge 1$. On natural numbers the recursion is that of $\mathbb{N}$.

::: mathlib
`Ordinal.instPow` · `Mathlib.SetTheory.Ordinal.Exponential`

The instance defines `a ^ b` as `1 - b` if `a = 0`, and otherwise by `limitRecOn b 1 (· * a)` with the supremum `⨆ x : Iio o, f x` at a limit `o`. The truncated subtraction of Section 1 gives `1 - 0 = 1` and `1 - b = 0` for `b ≥ 1`, so `zero_opow' : 0 ^ a = 1 - a` is the clause of the text. The equations are `opow_zero`, `opow_add_one` and `opow_limit (ha : a ≠ 0) (hb : IsSuccLimit b) : a ^ b = ⨆ x : Iio b, a ^ x.val`. The lemma `opow_natCast` says that the ordinal power with a natural exponent is the monoid power `a ^ n`.

<?decl Ordinal.instPow?>
:::

**Definition (Logarithm).** Let $b > 1$ and $x \neq 0$. The *logarithm* $\log_b x$ is the largest ordinal $c$ with $b^c \le x$. For $b \le 1$ or $x = 0$, set $\log_b x = 0$.

The theorem on logarithms below shows that the largest $c$ exists.

::: mathlib
`Ordinal.log` · `Mathlib.SetTheory.Ordinal.Exponential`

`log b x = sSup ((b ^ ·) ⁻¹' Iic x)`, the supremum of the $c$ with `b ^ c ≤ x`. For `b ≤ 1` this set is not bounded, and `sSup` of an unbounded set of ordinals is `0` by convention. So the junk values are `log_of_left_le_one (h : b ≤ 1) x : log b x = 0` and `log_zero_right b : log b 0 = 0`. The main lemma is the Galois-like connection `opow_le_iff_le_log (hb : 1 < b) (hx : x ≠ 0) : b ^ c ≤ x ↔ c ≤ log b x`, with its form `lt_opow_iff_log_lt`.

<?decl Ordinal.log?>
:::

### Theorems and proofs

**Lemma (Positivity).** If $\alpha > 0$, then $\alpha^\beta > 0$ for all $\beta$.

*Proof.* Induction on $\beta$. $\alpha^0 = 1 > 0$. If $\alpha^\beta > 0$, then $\alpha^\beta \alpha > 0$, as a product of nonempty well-orders is nonempty. At a limit, $\alpha^\lambda \ge \alpha^0 = 1$. $\square$

**Theorem (Normality).** Let $\alpha > 1$. Then $\beta \mapsto \alpha^\beta$ is strictly increasing and continuous at limits. In particular $\beta \le \alpha^\beta$ for all $\beta$.

*Proof.* Continuity is the limit clause. For each $\beta$, $\alpha^\beta < \alpha^\beta \alpha = \alpha^{\beta+1}$: indeed $\alpha^\beta \cdot 1 < \alpha^\beta \cdot \alpha$ by the monotonicity lemma of Section 1, since $\alpha^\beta > 0$ and $1 < \alpha$. Now show by induction on $\gamma$ that $\beta < \gamma$ implies $\alpha^\beta < \alpha^\gamma$. The case $\gamma = 0$ is empty. If $\gamma = \delta + 1$, then $\beta \le \delta$, so $\alpha^\beta \le \alpha^\delta < \alpha^{\delta + 1}$ by the hypothesis of induction. If $\gamma$ is a limit, then $\beta + 1 < \gamma$ and $\alpha^\beta < \alpha^{\beta+1} \le \sup_{\xi < \gamma} \alpha^\xi = \alpha^\gamma$.

For the last claim, use induction on $\beta$. The case $0$ is $0 \le 1$. If $\beta \le \alpha^\beta$, then $\beta + 1 \le \alpha^\beta + 1 \le \alpha^{\beta+1}$, since $\alpha^\beta < \alpha^{\beta+1}$. At a limit, $\lambda = \sup_{\beta < \lambda} \beta \le \sup_{\beta < \lambda} \alpha^\beta$. $\square$

::: mathlib
`Ordinal.isNormal_opow` · `Mathlib.SetTheory.Ordinal.Exponential`

`isNormal_opow (h : 1 < a) : IsNormal (a ^ ·)`. From it come `opow_lt_opow_iff_right (a1 : 1 < a) : a ^ b < a ^ c ↔ b < c` and `right_le_opow b (a1 : 1 < a) : b ≤ a ^ b`. In the base, the power is only monotone: `opow_le_opow_left c (ab : a ≤ b) : a ^ c ≤ b ^ c`. `opow_pos b (a0 : 0 < a) : 0 < a ^ b` is the positivity lemma.

<?decl Ordinal.isNormal_opow?>
:::

The proof of the laws uses one fact on suprema. Let $f$ be strictly increasing and continuous, $\lambda$ a limit, and $g$ monotone. Then $f(\lambda)$ is a limit, and $\sup_{\xi < f(\lambda)} g(\xi) = \sup_{\delta < \lambda} g(f(\delta))$. Indeed, each $\xi < f(\lambda) = \sup_{\delta < \lambda} f(\delta)$ is below some $f(\delta)$, so $g(\xi) \le g(f(\delta))$; and each $f(\delta)$ with $\delta < \lambda$ is below $f(\lambda)$. The value $f(\lambda)$ is a limit, since $\xi < f(\delta)$ gives $\xi + 1 \le f(\delta) < f(\delta + 1)$.

**Theorem (Laws of exponents).** For all $\alpha, \beta, \gamma$:
$$\alpha^{\beta + \gamma} = \alpha^\beta \cdot \alpha^\gamma, \qquad \alpha^{\beta \gamma} = (\alpha^\beta)^\gamma.$$

*Proof.* For $\alpha = 1$ all terms are $1$. For $\alpha = 0$, $0^\xi$ is $1$ if $\xi = 0$ and $0$ otherwise. Since $\beta + \gamma = 0$ if and only if $\beta = \gamma = 0$, and $\beta\gamma = 0$ if and only if $\beta = 0$ or $\gamma = 0$, both laws follow by cases. Let $\alpha > 1$. The proof of the first law is by induction on $\gamma$. The case $\gamma = 0$ is $\alpha^\beta = \alpha^\beta \cdot 1$. The successor step is
$$\alpha^{\beta + \gamma + 1} = \alpha^{\beta + \gamma} \alpha = \alpha^\beta \alpha^\gamma \alpha = \alpha^\beta \alpha^{\gamma + 1}.$$
Let $\gamma = \lambda$ be a limit. Apply the fact with $f = (\beta + \cdot)$ and $g = (\alpha^{\cdot})$. Then $\beta + \lambda$ is a limit, and
$$\alpha^{\beta + \lambda} = \sup_{\xi < \beta + \lambda} \alpha^\xi = \sup_{\delta < \lambda} \alpha^{\beta + \delta} = \sup_{\delta < \lambda} \alpha^\beta \alpha^\delta = \alpha^\beta \sup_{\delta < \lambda} \alpha^\delta = \alpha^\beta \alpha^\lambda.$$
For the fourth equality, $\alpha^\beta \cdot (\cdot)$ is normal by Section 1, as $\alpha^\beta > 0$. Its limit equation at $\alpha^\lambda$ and the fact with $f = (\alpha^{\cdot})$ give $\alpha^\beta \alpha^\lambda = \sup_{\xi < \alpha^\lambda} \alpha^\beta \xi = \sup_{\delta < \lambda} \alpha^\beta \alpha^\delta$.

For the second law, the case $\beta = 0$ gives $1 = 1^\gamma$. Let $\beta > 0$, so $\alpha^\beta > 1$. Induction on $\gamma$: the case $0$ is $1 = 1$. The successor step uses the first law:
$$\alpha^{\beta(\gamma + 1)} = \alpha^{\beta\gamma + \beta} = \alpha^{\beta\gamma} \alpha^\beta = (\alpha^\beta)^\gamma \alpha^\beta = (\alpha^\beta)^{\gamma + 1}.$$
At a limit $\lambda$, apply the fact with $f = (\beta \cdot)$, which is normal since $\beta > 0$:
$$\alpha^{\beta\lambda} = \sup_{\delta < \lambda} \alpha^{\beta\delta} = \sup_{\delta < \lambda} (\alpha^\beta)^\delta = (\alpha^\beta)^\lambda. \qquad \square$$

**Theorem (Logarithm and base-$b$ division).** Let $b > 1$ and $x \neq 0$. There is a largest $c$ with $b^c \le x$. For this $c$, there are unique $q, r$ with
$$x = b^c q + r, \qquad 0 < q < b, \qquad r < b^c.$$

*Proof.* By normality, $x < x + 1 \le b^{x+1}$. Let $c_0$ be the least ordinal with $x < b^{c_0}$. Then $c_0 \neq 0$, since $b^0 = 1 \le x$. If $c_0$ were a limit, then $b^\xi \le x$ for all $\xi < c_0$, and $b^{c_0} = \sup_{\xi < c_0} b^\xi \le x$, a contradiction. So $c_0 = c + 1$ with $b^c \le x < b^{c+1}$. Since the power is increasing, $c$ is the largest ordinal with $b^c \le x$.

Divide $x$ by $b^c \neq 0$ (Section 1): $x = b^c q + r$ with $r < b^c$, and the pair is unique. If $q = 0$, then $x = r < b^c$, a contradiction. If $q \ge b$, then $x \ge b^c b = b^{c+1}$, a contradiction. $\square$

::: mathlib
`Ordinal.div_opow_log_lt` · `Mathlib.SetTheory.Ordinal.Exponential`

The theorem is split into lemmas on `log b o`. `opow_log_le_self b (hx : x ≠ 0) : b ^ log b x ≤ x` and `lt_opow_succ_log_self (hb : 1 < b) x : x < b ^ succ (log b x)` give the two bounds. `div_opow_log_lt o (hb : 1 < b) : o / b ^ log b o < b` bounds the leading coefficient, and `mod_opow_log_lt_self b (ho : o ≠ 0) : o % b ^ log b o < o` gives the descent that Section 3 uses to define the normal form by recursion. `log_opow_mul_add (hb : 1 < b) (hv : v ≠ 0) (hw : w < b ^ u) : log b (b ^ u * v + w) = u + log b v` computes logarithms, and `log_opow (hb : 1 < b) x : log b (b ^ x) = x` is a special case.

<?decl Ordinal.div_opow_log_lt?>
:::

**Theorem (Commuting ordinals).** For ordinals $\alpha$ and $\beta$, $\alpha + \beta = \beta + \alpha$ if and only if there are an ordinal $\gamma$ and natural numbers $m, n$ with $\alpha = \gamma m$ and $\beta = \gamma n$.

*Proof.* If $\alpha = \gamma m$ and $\beta = \gamma n$, then $\alpha + \beta = \gamma (m + n) = \gamma (n + m) = \beta + \alpha$ by left distributivity.

For the converse, use induction on $\alpha + \beta$. Assume $\alpha + \beta = \beta + \alpha$ and, by symmetry, $\alpha \le \beta$. If $\alpha = 0$, take $\gamma = \beta$, $m = 0$, $n = 1$. Let $\alpha > 0$ and let $\delta = \beta - \alpha$, so $\alpha + \delta = \beta$. Then
$$\alpha + (\delta + \alpha) = \beta + \alpha = \alpha + \beta = \alpha + (\alpha + \delta),$$
so $\delta + \alpha = \alpha + \delta$ by left cancellation. Also $\alpha + \delta = \beta < \beta + \alpha = \alpha + \beta$, since $\alpha > 0$. The hypothesis of induction gives $\gamma, m, k$ with $\alpha = \gamma m$ and $\delta = \gamma k$. Then $\beta = \gamma m + \gamma k = \gamma (m + k)$. $\square$

::: mathlib
`Ordinal.addCommute_iff_eq_mul_natCast` · `Mathlib.SetTheory.Ordinal.Commute`

`AddCommute o₁ o₂ ↔ ∃ (o : Ordinal) (n₁ n₂ : ℕ), o * n₁ = o₁ ∧ o * n₂ = o₂`. The Mathlib proof is the proof above: well-founded induction on `o₁ + o₂`, the subtraction `o₂ - o₁` and left cancellation. The file cites Sierpiński, *Cardinal and Ordinal Numbers*.

<?decl Ordinal.addCommute_iff_eq_mul_natCast?>
:::

### Examples

**Example ($2^\omega = \omega$).** The limit clause gives $2^\omega = \sup_n 2^n = \omega$, since the $2^n$ are natural numbers and are not bounded in $\mathbb{N}$. In the same way $n^\omega = \omega$ for $2 \le n < \omega$; Mathlib has this as `Ordinal.opow_omega0` in `Mathlib.SetTheory.Ordinal.Principal`, and the general form `iSup_pow_natCast (ho : 0 < o) : ⨆ n : ℕ, o ^ n = o ^ ω`. The cardinal $2^{\aleph_0}$ of Chapter 5 is uncountable. The two notations differ, and Mathlib keeps them apart by the types `Ordinal` and `Cardinal`.

**Example (Small powers of $\omega$).** The ordinal $\omega^\omega = \sup_n \omega^n$ is the type of the polynomials with coefficients in $\mathbb{N}$, ordered by degree and then by the coefficients from the top. The first law gives $\omega^\omega \cdot \omega = \omega^{\omega + 1}$, and the second gives $(\omega^\omega)^\omega = \omega^{\omega^2}$.

**Example (A logarithm).** Let $x = \omega^3 \cdot 2 + \omega + 5$. Then $\log_\omega x = 3$: indeed $\omega^3 \le x$ and $x < \omega^3 \cdot 3 < \omega^4$. The base-$\omega$ division gives $q = 2$ and $r = \omega + 5$. With base $2$: since $2^\omega = \omega$, the largest $c$ with $2^c \le \omega^2$ is found from $2^{\omega \cdot 2} = (2^\omega)^2 = \omega^2$, so $\log_2 \omega^2 = \omega \cdot 2$, and $\omega^2 = 2^{\omega \cdot 2} \cdot 1 + 0$.

**Counterexample (The law $(\alpha\beta)^\gamma = \alpha^\gamma \beta^\gamma$ fails).** Take $\alpha = \omega$, $\beta = 2$, $\gamma = 2$. Then
$$(\omega \cdot 2)^2 = \omega \cdot 2 \cdot \omega \cdot 2 = \omega \cdot (2 \cdot \omega) \cdot 2 = \omega \cdot \omega \cdot 2 = \omega^2 \cdot 2,$$
by associativity and $2 \cdot \omega = \omega$. But $\omega^2 \cdot 2^2 = \omega^2 \cdot 4 > \omega^2 \cdot 2$. A proof of this law would need a commutative product.

**Counterexample (The hypothesis $\alpha > 1$).** For $\alpha = 1$, the map $\beta \mapsto 1^\beta = 1$ is constant, and for $\alpha = 0$ it is not monotone: $0^0 = 1 > 0 = 0^1$. So `isNormal_opow` needs `1 < a`, and `log 1 x = 0` for all `x` is junk.

### The library around it

The file also has `opow_le_opow_right`, `opow_dvd_opow`, `log_mono_right`, `log_le_self`, `natCast_log` (the logarithm of naturals is `Nat.log`) and `opow_mul_add_lt_opow`, which bounds the terms of a normal form.

Common errors of a learner:

- `a ^ b` with `a b : Ordinal` is the ordinal power. With `b : ℕ` it is the monoid power. `opow_natCast` converts between them; `simp` uses it.
- The power is not commutative in the base: $(\omega 2)^2 \neq \omega^2 2^2$, and `mul_pow` does not apply.
- `log b x` is junk for `b ≤ 1` and for `x = 0`. The lemmas need `1 < b` and `x ≠ 0`.
- The ordinal $2^\omega$ is countable. The cardinal `2 ^ ℵ₀` is a different object.

### Exercises

1. (A) Compute $\omega^{\omega} \cdot \omega^2$, $(\omega^2)^\omega$, $(\omega + 1)^2$ and $2^{\omega + 3}$.
2. (A) Show that $\alpha^\beta$ is a limit ordinal when $\alpha$ is a limit and $\beta > 0$.
3. (A) Compute $\log_\omega (\omega^\omega + \omega^5 \cdot 3)$ and $\log_2 (\omega^\omega)$.
4. (B) Prove $(\omega + 1)^n = \omega^n + \omega^{n-1} + \cdots + \omega + 1$ for $n \ge 1$. Hint: induction on $n$, and $(\omega^n + \cdots + 1) \cdot \omega = \omega^{n+1}$.
5. (B) Prove $\log_b (b^u v + w) = u + \log_b v$ for $b > 1$, $v \neq 0$ and $w < b^u$.
6. (B) Show that $\alpha^\beta < \alpha^\gamma$ need not follow from $\beta < \gamma$ when $\alpha \le 1$, and that $\alpha < \alpha'$ does not imply $\alpha^\omega < \alpha'^\omega$. Hint: $2^\omega$ and $3^\omega$.
7. (C) Use the theorem on commuting ordinals to find all $\alpha, \beta < \omega^2$ with $\alpha + \beta = \beta + \alpha$.
8. (C) Show that $\alpha \cdot \beta = \beta \cdot \alpha$ for $\alpha = \omega^{\omega}$ and $\beta = \omega^{\omega \cdot 2}$, but not for $\alpha = \omega$ and $\beta = \omega + 1$.

### Notes and history

Cantor defined the exponentiation of ordinals in the *Beiträge*. Jech, *Set Theory*, Chapter 2, and Kunen, *Set Theory*, Chapter I, give it in this form. The theorem on commuting ordinals is in Sierpiński, *Cardinal and Ordinal Numbers*, the reference of the Mathlib file. The ordinal logarithm is rare in textbooks; Mathlib uses it to define the Cantor normal form by recursion.

### Reference

<?reference?>
