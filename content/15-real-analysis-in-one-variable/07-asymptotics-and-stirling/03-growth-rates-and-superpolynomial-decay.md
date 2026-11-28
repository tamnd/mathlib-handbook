---
title: Growth rates and superpolynomial decay
kind: api
modules:
  - Mathlib.Analysis.Asymptotics.LinearGrowth
  - Mathlib.Analysis.Asymptotics.ExpGrowth
  - Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
  - Mathlib.Analysis.SpecialFunctions.CompareExp
explains:
  E2: [LinearGrowth.linearGrowthSup_le_iff, ExpGrowth.expGrowthSup_pow, ExpGrowth.expGrowthSup_add, ExpGrowth.expGrowthInf_inv, Asymptotics.SuperpolynomialDecay.mul, Asymptotics.superpolynomialDecay_iff_isBigO, Complex.IsExpCmpFilter.of_boundedUnder_abs_im, Complex.IsExpCmpFilter.isLittleO_im_pow_exp_re]
  E1: auto
families: []
requires: [V02, V13, V15.C01, V15.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Growth rates and superpolynomial decay

### Overview

Section 1 of this chapter compares two functions with $O$, $o$ and $\sim$. Often a single number describes the growth of a sequence better than a comparison. The sequence $3^n$ grows at the exponential rate $\log 3$, and the sequence $5n + \sin n$ grows at the linear rate $5$. This section treats the modules of Mathlib that define these rates. The linear growth of a sequence $u$ is the pair $\liminf u_n/n$ and $\limsup u_n/n$. The exponential growth of a sequence $u$ is the pair $\liminf \frac{1}{n}\log u_n$ and $\limsup \frac{1}{n}\log u_n$. The values are extended reals, so that every sequence has a growth rate.

The section then treats two notions of fast decay and slow growth. A function has *superpolynomial decay* when it is small compared with every power of a parameter, as $e^{-x}$ is small compared with $x^{-n}$ for every $n$. The last module compares complex powers $z^a$ with exponentials $e^{bz}$ along filters on $\mathbb{C}$ on which the real part tends to infinity. It extends the scale of growth of Section 1 from the real line to regions of the complex plane.

### The library around it

#### Linear growth

The module `Mathlib.Analysis.Asymptotics.LinearGrowth` defines, for a sequence `u : ℕ → R`, the two numbers

$$\mathrm{linearGrowthInf}(u) = \liminf_{n \to \infty} \frac{u_n}{n}, \qquad \mathrm{linearGrowthSup}(u) = \limsup_{n \to \infty} \frac{u_n}{n}.$$

They are `LinearGrowth.linearGrowthInf` and `LinearGrowth.linearGrowthSup`. The definition needs only a conditionally complete lattice `R` with a division and a cast from `ℕ`, but nearly all the lemmas take `R = EReal`, the extended reals $[-\infty, \infty]$. In `EReal` every sequence has a `liminf` and a `limsup`, so the two rates always exist. The basic values are in the table.

| Lean name | Statement |
|---|---|
| `LinearGrowth.linearGrowthSup_const_mul_self` | the sequence $a n$ has upper linear growth $a$ |
| `LinearGrowth.linearGrowthInf_const` | a finite constant sequence has lower linear growth $0$ |
| `LinearGrowth.linearGrowthSup_top` | the constant sequence $\infty$ has growth $\infty$ |
| `LinearGrowth.linearGrowthInf_le_linearGrowthSup` | the lower rate is at most the upper rate (under a boundedness side condition) |
| `LinearGrowth.linearGrowthInf_neg` | $\mathrm{linearGrowthInf}(-u) = -\mathrm{linearGrowthSup}(u)$ |
| `LinearGrowth.linearGrowthSup_inv` | $\mathrm{linearGrowthSup}(-u) = -\mathrm{linearGrowthInf}(u)$ |

The working form of the definition is a pair of eventual bounds. The rates are characterized by comparison of $u_n$ with the lines $b n$.

**Theorem.** For `u : ℕ → EReal` and $a \in [-\infty, \infty]$, $\mathrm{linearGrowthSup}(u) \le a$ if and only if for every $b > a$, eventually $u_n \le b n$.

*Proof.* Suppose $\limsup u_n/n \le a$ and $b > a$. Then eventually $u_n/n < b$, so $u_n \le bn$. Conversely, if eventually $u_n \le bn$, then $\limsup u_n/n \le b$. This holds for every $b > a$, so the $\limsup$ is at most $a$. $\square$

This is `LinearGrowth.linearGrowthSup_le_iff`. The three other forms are `LinearGrowth.le_linearGrowthSup_iff`, `LinearGrowth.linearGrowthInf_le_iff` and `LinearGrowth.le_linearGrowthInf_iff`, with "frequently" in place of "eventually" for the $\liminf$. The one-way lemmas `LinearGrowth.eventually_le_mul`, `LinearGrowth.frequently_mul_le`, `Eventually.linearGrowthSup_le` and `Frequently.le_linearGrowthSup` state the separate directions. The names with the prefixes Eventually and Frequently are in the root namespace, so dot notation on a hypothesis `h : ∀ᶠ n in atTop, _` does not find them.

The rates respect the order and the lattice operations. `LinearGrowth.linearGrowthSup_monotone` and `LinearGrowth.linearGrowthSup_eventually_monotone` give monotonicity, and `LinearGrowth.linearGrowthSup_congr` shows that the rate depends only on the tail of the sequence. The upper rate of a pointwise maximum is the maximum of the upper rates (`LinearGrowth.linearGrowthSup_sup`), and the same holds for finite suprema (`LinearGrowth.linearGrowthSup_iSup`, `LinearGrowth.linearGrowthSup_biSup`). So `LinearGrowth.linearGrowthSupBotHom` packs the upper rate as a `SupBotHom`, a map that keeps binary suprema and the bottom element. Dually, `LinearGrowth.linearGrowthInfTopHom` is an `InfTopHom`. For sums the rates are subadditive, with side conditions that exclude the undefined form $\infty - \infty$: `LinearGrowth.linearGrowthSup_add_le` gives $\mathrm{linearGrowthSup}(u + v) \le \mathrm{linearGrowthSup}(u) + \mathrm{linearGrowthSup}(v)$, and `LinearGrowth.le_linearGrowthInf_add` gives the reverse inequality for the lower rates.

The last part of the module treats subsequences. For a monotone sequence $u$ and an integer $m \ne 0$, the sequence $n \mapsto u_{mn}$ has $m$ times the rate of $u$ (`Monotone.linearGrowthSup_comp_mul`, `Monotone.linearGrowthInf_comp_mul`). More generally, if $v_n / n \to a$ with $a \ne 0$ and $a$ finite, then $u \circ v$ has $a$ times the rate of $u$ (`Monotone.linearGrowthSup_comp`). Monotonicity is needed: without it, $u \circ v$ can pick the small terms of an oscillating sequence. A positive lower rate forces $u_n \to \infty$ (`LinearGrowth.tendsto_atTop_of_linearGrowthInf_pos`).

#### Exponential growth

The module `Mathlib.Analysis.Asymptotics.ExpGrowth` treats sequences `u : ℕ → ℝ≥0∞` of extended nonnegative reals. It defines `ExpGrowth.expGrowthInf` and `ExpGrowth.expGrowthSup` as the `liminf` and the `limsup` of $\frac{1}{n}\log u_n$. The logarithm is `ENNReal.log`, with values in `EReal`, $\log 0 = -\infty$ and $\log \infty = \infty$. The two lemmas `ExpGrowth.expGrowthInf_def` and `ExpGrowth.expGrowthSup_def` reduce the exponential rates to the linear rates of `ENNReal.log ∘ u`, and most proofs of the module go through this reduction. The exponential `EReal.exp` is the inverse map from `EReal` to `ℝ≥0∞`.

**Theorem.** For $b \in [0, \infty]$, the sequence $b^n$ has exponential growth $\log b$.

*Proof.* The logarithm turns the power into a product: $\log(b^n) = n \log b$ (`ENNReal.log_pow`). So $\frac{1}{n}\log b^n = \log b$ for $n \ge 1$, a constant sequence, and its `liminf` and `limsup` are $\log b$. $\square$

This is `ExpGrowth.expGrowthSup_pow`, with the twin `ExpGrowth.expGrowthInf_pow`. In the same way `ExpGrowth.expGrowthSup_exp` computes the rate $a$ of $e^{an}$, `ExpGrowth.expGrowthSup_const` gives rate $0$ for a constant in $(0, \infty)$, and `ExpGrowth.expGrowthSup_zero` gives rate $-\infty$ for the zero sequence. The characterizations `ExpGrowth.expGrowthSup_le_iff`, `ExpGrowth.le_expGrowthInf_iff` and their companions compare $u_n$ with $e^{bn}$, as the linear ones compare $u_n$ with $bn$.

The exponential rate forgets constant factors: if eventually $u_n \le b v_n$ with $b < \infty$, then the rate of $u$ is at most the rate of $v$ (`ExpGrowth.expGrowthSup_le_of_eventually_le`). This gives the rule for sums.

**Theorem.** $\mathrm{expGrowthSup}(u + v) = \max(\mathrm{expGrowthSup}(u), \mathrm{expGrowthSup}(v))$.

*Proof.* Since $u \le u + v$ and $v \le u + v$, the right side is at most the left side. Conversely, $u_n + v_n \le 2 \max(u_n, v_n)$. The factor $2$ does not change the rate, so the rate of $u + v$ is at most the rate of $\max(u, v)$. This rate is the maximum of the two rates by `ExpGrowth.expGrowthSup_sup`. $\square$

This is `ExpGrowth.expGrowthSup_add`, and `ExpGrowth.expGrowthSup_sum` extends it to finite sums. The lower rate satisfies only an inequality, `ExpGrowth.le_expGrowthInf_add`. For products the rates add, as subadditive bounds: `ExpGrowth.expGrowthSup_mul_le` and `ExpGrowth.le_expGrowthInf_mul`. The inverse sequence exchanges the two rates and changes the sign.

**Theorem.** $\mathrm{expGrowthInf}(u^{-1}) = -\mathrm{expGrowthSup}(u)$.

*Proof.* In `ℝ≥0∞` the logarithm satisfies $\log(x^{-1}) = -\log x$, also for $x = 0$ and $x = \infty$. So $\frac{1}{n}\log u_n^{-1} = -\frac{1}{n}\log u_n$, and the `liminf` of the negative of a sequence is the negative of its `limsup`. $\square$

This is `ExpGrowth.expGrowthInf_inv`, and `ExpGrowth.expGrowthSup_inv` is the twin. The bundled maps `ExpGrowth.expGrowthSupBotHom` and `ExpGrowth.expGrowthInfTopHom`, and the lemmas on subsequences `Monotone.expGrowthSup_comp_mul` and `Monotone.expGrowthSup_comp`, repeat the pattern of the linear module.

#### Superpolynomial decay

The module `Mathlib.Analysis.Asymptotics.SuperpolynomialDecay` defines the predicate `Asymptotics.SuperpolynomialDecay l k f`. Here `l` is a filter, `k` is the parameter and `f` is the function. The definition is

$$\forall n \in \mathbb{N},\quad k(x)^n f(x) \to 0 \text{ along } l.$$

The typical case is `l = atTop` on `ℝ` and `k = id`: then $f$ has superpolynomial decay when $x^n f(x) \to 0$ for every $n$. The function $e^{-x}$ is the standard example.

The closure lemmas are direct. `Asymptotics.SuperpolynomialDecay.add`, `Asymptotics.SuperpolynomialDecay.const_mul` and `Asymptotics.SuperpolynomialDecay.mul_const` show that these functions form a vector space. `Asymptotics.SuperpolynomialDecay.param_mul` and `Asymptotics.SuperpolynomialDecay.param_pow_mul` multiply by $k$ and by $k^n$, and `Asymptotics.SuperpolynomialDecay.polynomial_mul` multiplies by a polynomial in $k$. The squeeze lemma `Asymptotics.SuperpolynomialDecay.trans_eventuallyLE` and the comparison `Asymptotics.SuperpolynomialDecay.trans_abs_le` transfer the decay to a smaller function.

**Theorem.** If $f$ and $g$ have superpolynomial decay, then $fg$ has superpolynomial decay.

*Proof.* The case $n = 0$ of the definition for $g$ says $g \to 0$. For each $n$, $k^n f g = (k^n f) \cdot g$ is a product of two functions that tend to $0$, so it tends to $0$. $\square$

This is `Asymptotics.SuperpolynomialDecay.mul`. When `k` tends to infinity in an ordered field, the definition has many equivalent forms: with integer powers (`Asymptotics.superpolynomialDecay_iff_zpow_tendsto_zero`), with absolute values (`Asymptotics.superpolynomialDecay_iff_abs_tendsto_zero`), with bounded products (`Asymptotics.superpolynomialDecay_iff_abs_isBoundedUnder`), and in the language of Section 1.

**Theorem.** Suppose $k \to \infty$ along $l$, in a normed ordered field. Then $f$ has superpolynomial decay if and only if $f = O(k^z)$ for every integer $z$.

*Proof.* Suppose $f$ has superpolynomial decay and let $z \in \mathbb{Z}$. By the form with integer powers, $k^{-z} f \to 0$, so eventually $|k^{-z} f| \le 1$, that is $|f| \le |k^z|$. Conversely, suppose $f = O(k^{-(n+1)})$. Then eventually $|k^n f| \le C |k|^{-1}$, and $|k|^{-1} \to 0$. $\square$

This is `Asymptotics.superpolynomialDecay_iff_isBigO`, and `Asymptotics.superpolynomialDecay_iff_isLittleO` is the form with $o$. The parameter itself can be absorbed: `Asymptotics.superpolynomialDecay_param_mul_iff` says that $kf$ has superpolynomial decay if and only if $f$ has it.

#### Powers against exponentials in the complex plane

The module `Mathlib.Analysis.SpecialFunctions.CompareExp` extends the comparison $x^a = o(e^{bx})$ of Section 1 to complex variables. The complex power $z^a$ does not have a good limit along every filter on $\mathbb{C}$, so the module fixes a class of filters. A filter `l` on `ℂ` is an *exponential comparison filter*, the structure `Complex.IsExpCmpFilter`, when two conditions hold:

1. $\operatorname{Re} z \to \infty$ along $l$ (the field `Complex.IsExpCmpFilter.tendsto_re`);
2. for every $n$, $(\operatorname{Im} z)^n = O(e^{\operatorname{Re} z})$ along $l$ (the field `Complex.IsExpCmpFilter.isBigO_im_pow_re`).

The second condition says that the imaginary part grows more slowly than any exponential of the real part. The constructors give it from simpler hypotheses: `Complex.IsExpCmpFilter.of_isBigO_im_re_rpow` and `Complex.IsExpCmpFilter.of_isBigO_im_re_pow` take $\operatorname{Im} z = O((\operatorname{Re} z)^r)$, and `Complex.IsExpCmpFilter.of_boundedUnder_im` takes a bounded imaginary part.

**Theorem.** If $\operatorname{Re} z \to \infty$ and $|\operatorname{Im} z|$ is bounded along $l$, then $l$ is an exponential comparison filter.

*Proof.* Let $|\operatorname{Im} z| \le C$ eventually. Then $|(\operatorname{Im} z)^n| \le C^n$, so $(\operatorname{Im} z)^n = O(1)$. Since $\operatorname{Re} z \to \infty$, eventually $e^{\operatorname{Re} z} \ge 1$, so $1 = O(e^{\operatorname{Re} z})$. The transitivity of $O$ gives the second condition. $\square$

This is `Complex.IsExpCmpFilter.of_boundedUnder_abs_im`. The first condition of the structure gives `Complex.IsExpCmpFilter.tendsto_norm`, $|z| \to \infty$, and `Complex.IsExpCmpFilter.eventually_ne`, $z \ne 0$ eventually. The $O$ bound of the second condition improves to an $o$ bound.

**Theorem.** Along an exponential comparison filter, $(\operatorname{Im} z)^n = o(e^{\operatorname{Re} z})$ for every $n$.

*Proof.* The condition with $2n$ gives $((\operatorname{Im} z)^n)^2 = O(e^{\operatorname{Re} z})$. Since $e^{\operatorname{Re} z} \to \infty$, $e^{\operatorname{Re} z} = o((e^{\operatorname{Re} z})^2)$. So $((\operatorname{Im} z)^n)^2 = o((e^{\operatorname{Re} z})^2)$, and a square root of both sides gives the claim (`Asymptotics.IsLittleO.of_pow`). $\square$

This is `Complex.IsExpCmpFilter.isLittleO_im_pow_exp_re`. The main lemma of the module is `Complex.IsExpCmpFilter.isLittleO_log_norm_re`: $\log|z| = o(\operatorname{Re} z)$. From it, `Complex.IsExpCmpFilter.isTheta_cpow_exp_re_mul_log` gives $z^a = \Theta(e^{\operatorname{Re}(a) \log|z|})$, and the comparisons follow.

| Lean name | Statement along $l$ |
|---|---|
| `Complex.IsExpCmpFilter.isLittleO_cpow_exp` | $z^a = o(e^{bz})$ for $b > 0$ |
| `Complex.IsExpCmpFilter.isLittleO_exp_cpow` | $e^{bz} = o(z^a)$ for $b < 0$ |
| `Complex.IsExpCmpFilter.isLittleO_cpow_mul_exp` | $z^{a_1} e^{b_1 z} = o(z^{a_2} e^{b_2 z})$ for real $b_1 < b_2$ |
| `Complex.IsExpCmpFilter.isLittleO_pow_mul_exp` | the same with natural powers |
| `Complex.IsExpCmpFilter.isLittleO_zpow_mul_exp` | the same with integer powers |

The comparison of $z^{a_1} e^{b_1 z}$ with $z^{a_2} e^{b_2 z}$ uses $|e^{bz}| = e^{b \operatorname{Re} z}$ (`Complex.norm_exp`): the exponentials differ by the factor $e^{(b_2 - b_1)\operatorname{Re} z}$, which beats every power of $|z|$ by the main lemma.

#### Common errors

1. Reading `LinearGrowth.linearGrowthSup_inv` as a statement about $1/u$. The sequence is `-u`, the negation in `EReal`, although the name says "inv". For the reciprocal of an `ℝ≥0∞` sequence, use `ExpGrowth.expGrowthSup_inv`.
2. Forgetting the side conditions of the sum and product rules. In `EReal` the sum $-\infty + \infty$ is $-\infty$ (`EReal.bot_add`), so `LinearGrowth.linearGrowthSup_add_le` needs hypotheses that exclude this case.
3. Applying the equivalences of superpolynomial decay without the hypothesis `Tendsto k l atTop`. The definition itself does not ask for it, but the forms with integer powers, with $o$ and with $O$ need it.

### Exercises

1. (A) Compute the linear growth rates of $u_n = 3n + (-1)^n n$ and the exponential growth rates of $u_n = 2^n + 5^n$.
2. (A) Show that a constant sequence $b \in (0, \infty)$ has exponential growth $0$, and that the zero sequence has exponential growth $-\infty$.
3. (B) Let $u$ be monotone with $\mathrm{expGrowthSup}(u) = a$. Show that $n \mapsto u_{n^2}$ can have infinite upper rate, and explain why `Monotone.expGrowthSup_comp` does not apply.
4. (B) Show that $f(x) = e^{-\sqrt{x}}$ has superpolynomial decay along `atTop` with parameter $x$. Hint: compare $x^n e^{-\sqrt x}$ with $y^{2n} e^{-y}$ for $y = \sqrt{x}$.
5. (B) Show that the filter of the points $z$ with $\operatorname{Re} z \to \infty$ inside the half strip $|\operatorname{Im} z| \le 1$ is an exponential comparison filter, and deduce that $z^{10} = o(e^{z/2})$ along it.
6. (C) Show that $\log|z| = o(\operatorname{Re} z)$ along an exponential comparison filter. Hint: split into the cases $|\operatorname{Im} z| \le \operatorname{Re} z$ and $|\operatorname{Im} z| > \operatorname{Re} z$, and use $|z| \le \sqrt{2}\max(\operatorname{Re} z, |\operatorname{Im} z|)$.

### Reference

<?reference?>
