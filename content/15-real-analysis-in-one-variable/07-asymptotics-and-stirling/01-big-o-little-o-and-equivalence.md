---
title: Big O, little o and equivalence
kind: theory
modules:
  - Mathlib.Analysis.Asymptotics.Defs
  - Mathlib.Analysis.Asymptotics.Basic
  - Mathlib.Analysis.Asymptotics.Arith
  - Mathlib.Analysis.Asymptotics.Ring
  - Mathlib.Analysis.Asymptotics.Lemmas
  - Mathlib.Analysis.Asymptotics.Theta
  - Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
  - Mathlib.Analysis.Asymptotics.SpecificAsymptotics
  - Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
explains:
  E3: [Asymptotics.IsBigO, Asymptotics.IsLittleO, Asymptotics.IsTheta, Asymptotics.IsEquivalent]
  E2: [Asymptotics.IsBigOWith, Asymptotics.isBigO_iff, Asymptotics.isLittleO_iff, Asymptotics.IsLittleO.isBigO, Asymptotics.IsBigO.trans, Asymptotics.IsLittleO.trans_isBigO, Asymptotics.IsBigO.trans_isLittleO, Asymptotics.IsLittleO.trans, Asymptotics.IsBigO.add, Asymptotics.IsLittleO.add, Asymptotics.IsBigO.mul, Asymptotics.IsLittleO.mul_isBigO, Asymptotics.isLittleO_iff_tendsto, Asymptotics.IsEquivalent.mul, Asymptotics.IsEquivalent.div, Asymptotics.isEquivalent_iff_tendsto_one, Asymptotics.IsEquivalent.isTheta, isLittleO_log_rpow_atTop, isLittleO_pow_exp_pos_mul_atTop]
  E1: auto
families: []
requires: [V02, V13, V15.C01, V15.C02, V15.C03, V15.C04, V15.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Big O, little o and equivalence

### Overview

The derivative says that $f(x) - f(x_0) - f'(x_0)(x - x_0)$ is small compared with $x - x_0$, and the Peano form of Taylor's theorem says that $f(x) - P_n(x)$ is small compared with $(x - x_0)^n$. Landau's symbols give a common notation for such statements: $f = O(g)$ means that $|f|$ is at most a constant times $|g|$, $f = o(g)$ means that $f/g \to 0$, and $f \sim g$ means that $f/g \to 1$.

A comparison is always made along a limit: $n \to \infty$, $x \to \infty$, $x \to x_0$ or $x \to x_0^+$. Mathlib makes the limit a parameter, a filter, so that one definition and one set of rules serve all cases. This section gives the definitions in that form, the rules to compute with them, and the scale of growth $\log x \ll x^a \ll e^x$.

### Definitions

The volume on general topology defines filters. A *filter* $l$ on a set $\alpha$ is a family of subsets of $\alpha$ that contains $\alpha$ and is closed under finite intersections and under supersets. A property $P$ holds *eventually along $l$* if $\{x : P(x)\} \in l$. If $P$ and $Q$ hold eventually, then $P \wedge Q$ holds eventually. The filters of this section are:

- `atTop` on $\mathbb{N}$ or $\mathbb{R}$: a set belongs to it if it contains a ray $[N, \infty)$. Eventually along `atTop` means "for all large $n$" or "for all large $x$".
- `nhds x₀` on $\mathbb{R}$: a set belongs to it if it contains an interval $(x_0 - \delta, x_0 + \delta)$. Eventually means "for all $x$ near $x_0$".
- `nhdsWithin x₀ s`: a set belongs to it if it contains $(x_0 - \delta, x_0 + \delta) \cap s$. For $s = (x_0, \infty)$ this is the limit from the right.

Below, $f, g, u, v$ are real functions on $\alpha$ and $l$ is a filter on $\alpha$.

**Definition (Big O).** $f = O(g)$ along $l$ if there is a constant $C$ such that eventually along $l$, $|f(x)| \le C |g(x)|$. For a fixed $C$, Mathlib says that $f$ is *$O(g)$ with constant $C$*.

**Definition (Little o).** $f = o(g)$ along $l$ if for every $\varepsilon > 0$, eventually along $l$, $|f(x)| \le \varepsilon |g(x)|$.

**Definition (Big Theta).** $f = \Theta(g)$ along $l$ if $f = O(g)$ and $g = O(f)$ along $l$.

**Definition (Asymptotic equivalence).** $u \sim v$ along $l$ if $u - v = o(v)$ along $l$.

So $f = o(g)$ is $O(g)$ with every positive constant, and $u \sim v$ says that the error $u - v$ is small compared with $v$.

::: mathlib
`Asymptotics.IsBigO` · `Mathlib.Analysis.Asymptotics.Defs`

The relation `f =O[l] g`, notation for `Asymptotics.IsBigO l f g`. It is defined as `∃ c, IsBigOWith c l f g`, where `Asymptotics.IsBigOWith c l f g` means `∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖`. The lemma `isBigO_iff` unfolds both steps. The functions take values in any normed spaces, and the two codomains can differ. On `ℝ` the norm is the absolute value.

<?decl Asymptotics.IsBigO?>
:::

::: mathlib
`Asymptotics.IsLittleO` · `Mathlib.Analysis.Asymptotics.Defs`

The relation `f =o[l] g`, defined as `∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c l f g`; `isLittleO_iff` unfolds it. The definition uses no division, so it makes sense where `g` vanishes. The relation `f =Θ[l] g` is `Asymptotics.IsTheta`, defined as `f =O[l] g ∧ g =O[l] f`.

<?decl Asymptotics.IsLittleO?>
:::

::: mathlib
`Asymptotics.IsEquivalent` · `Mathlib.Analysis.Asymptotics.AsymptoticEquivalent`

The relation `IsEquivalent l u v`, defined as `(u - v) =o[l] v`. The notation `u ~[l] v` is scoped: it is available after `open Asymptotics`. Part 3 of the theorem on quotients is `isEquivalent_iff_tendsto_one`, with the hypothesis `∀ᶠ x in l, v x ≠ 0`.

<?decl Asymptotics.IsEquivalent?>
:::

### Theorems and proofs

**Proposition (Basic implications).** Along any filter:

1. if $f = o(g)$, then $f = O(g)$;
2. if $u \sim v$, then $u = \Theta(v)$; more precisely, eventually $\frac12 |v(x)| \le |u(x)| \le \frac32 |v(x)|$.

*Proof.* 1. Take $\varepsilon = 1$ in the definition of $o$. Then $C = 1$ works.

2. With $\varepsilon = \frac12$: eventually $|u - v| \le \frac12 |v|$. The triangle inequality gives $|u| \le \frac32 |v|$ and $|v| \le |u| + \frac12 |v|$, so $\frac12 |v| \le |u|$. $\square$

**Theorem (Transitivity).** Along any filter:

1. if $f = O(g)$ and $g = O(k)$, then $f = O(k)$;
2. if $f = o(g)$ and $g = O(k)$, then $f = o(k)$;
3. if $f = O(g)$ and $g = o(k)$, then $f = o(k)$.

*Proof.* The constants can be taken positive, since a larger constant keeps a bound true. Two properties that hold eventually hold together eventually.

1. Eventually $|f| \le C |g|$ and $|g| \le D |k|$, so $|f| \le C D |k|$.

2. Let $\varepsilon > 0$ and let $|g| \le D |k|$ eventually. The definition of $f = o(g)$ with $\varepsilon / D$ gives $|f| \le \frac{\varepsilon}{D} |g| \le \varepsilon |k|$ eventually.

3. Let $\varepsilon > 0$. Eventually $|f| \le C |g|$ and $|g| \le \frac{\varepsilon}{C} |k|$, so $|f| \le \varepsilon |k|$. $\square$

**Theorem (Sums and products).** Along any filter:

1. if $f_1 = O(g)$ and $f_2 = O(g)$, then $f_1 + f_2 = O(g)$; the same holds with $o$ in place of $O$;
2. if $f_1 = O(g_1)$ and $f_2 = O(g_2)$, then $f_1 f_2 = O(g_1 g_2)$;
3. if $f_1 = o(g_1)$ and $f_2 = O(g_2)$, then $f_1 f_2 = o(g_1 g_2)$.

*Proof.* 1. Eventually $|f_1| \le C_1 |g|$ and $|f_2| \le C_2 |g|$, so $|f_1 + f_2| \le (C_1 + C_2)|g|$. For $o$, given $\varepsilon > 0$ use $\varepsilon/2$ for both.

2. With $C_1, C_2 \ge 0$: eventually $|f_1 f_2| = |f_1||f_2| \le C_1 C_2 |g_1 g_2|$.

3. Let $\varepsilon > 0$ and let $|f_2| \le C |g_2|$ eventually, with $C > 0$. Eventually $|f_1| \le \frac{\varepsilon}{C} |g_1|$. Then $|f_1 f_2| \le \varepsilon |g_1 g_2|$. $\square$

::: mathlib
`Asymptotics.IsBigO.trans` · `Mathlib.Analysis.Asymptotics.Basic`

Transitivity is `IsBigO.trans`, `IsLittleO.trans_isBigO`, `IsBigO.trans_isLittleO` and `IsLittleO.trans`, the steps of a `calc` proof. The sums are `IsBigO.add` and `IsLittleO.add`, and the products are `IsBigO.mul` and `IsLittleO.mul_isBigO`. The implication $o \Rightarrow O$ is `IsLittleO.isBigO`. Part 1 of the theorem on quotients is `isLittleO_iff_tendsto`.

<?decl Asymptotics.IsBigO.trans?>
:::

**Theorem (Quotients).** Assume that eventually $g(x) \ne 0$ and $v(x) \ne 0$. Then:

1. $f = o(g)$ if and only if $f(x)/g(x) \to 0$ along $l$;
2. $f = O(g)$ if and only if $f/g$ is eventually bounded;
3. $u \sim v$ if and only if $u(x)/v(x) \to 1$ along $l$.

*Proof.* 1. Where $g(x) \ne 0$, $|f(x)| \le \varepsilon |g(x)|$ is equivalent to $|f(x)/g(x)| \le \varepsilon$, so the definition of $o$ is the definition of $f/g \to 0$. 2. The same with a fixed $C$. 3. $\frac{u - v}{v} = \frac{u}{v} - 1$, so part 1 applies. $\square$

**Theorem (Rules for equivalence).** Along any filter:

1. $\sim$ is an equivalence relation;
2. if $t \sim u$ and $v \sim w$, then $tv \sim uw$, and $t/v \sim u/w$ when $v$ and $w$ are eventually nonzero;
3. if $u \sim v$ and $u \to c$, then $v \to c$;
4. if $u \sim v$ and $w = o(v)$, then $u + w \sim v$.

*Proof.* 1. Reflexivity: $u - u = 0 = o(v)$. Symmetry: if $u - v = o(v)$, then $v = O(u)$ by the proposition, so $v - u = o(v) = o(u)$ by transitivity. Transitivity: if $u - v = o(v)$ and $v - w = o(w)$, then $v = O(w)$, so $u - w = (u - v) + (v - w) = o(w)$.

2. $tv - uw = (t - u) v + u (v - w)$, with $(t - u)v = o(u) \cdot O(w) = o(uw)$ and $u(v - w) = O(u) \cdot o(w) = o(uw)$. For the quotient, $\frac1v - \frac1w = \frac{w - v}{vw}$, where $w - v = o(w)$ and $\frac{1}{vw} = O(\frac{1}{w^2})$ since $|v| \ge \frac12 |w|$ eventually. So $\frac1v \sim \frac1w$, and the product rule applies to $t \cdot \frac1v$.

3. Eventually $|v(x)| \le 2|u(x)|$, by the proposition. Since $u \to c$, $u$ is eventually bounded, say $|u| \le B$, so $|v| \le 2B$ eventually. Let $\varepsilon > 0$. Eventually $|u(x) - v(x)| \le \varepsilon |v(x)| \le 2B\varepsilon$ and $|u(x) - c| \le \varepsilon$. Then $|v(x) - c| \le (2B + 1)\varepsilon$.

4. $(u + w) - v = (u - v) + w$, a sum of two functions that are $o(v)$. $\square$

::: mathlib
`Asymptotics.IsEquivalent.mul` · `Mathlib.Analysis.Asymptotics.AsymptoticEquivalent`

The rules are `IsEquivalent.refl`, `.symm`, `.trans`, `.mul`, `.div`, `.pow`, `.tendsto_nhds` and `.add_isLittleO`. `IsEquivalent.div` needs no hypothesis that the functions are nonzero, because of the convention `x / 0 = 0`. The link to $\Theta$ is `IsEquivalent.isTheta`.

<?decl Asymptotics.IsEquivalent.mul?>
:::

**Theorem (The scale of growth).**

1. For $k \in \mathbb{N}$ and $r > 1$, $n^k = o(r^n)$ as $n \to \infty$.
2. For $k \in \mathbb{N}$, $x^k = o(e^x)$ as $x \to \infty$.
3. For $a > 0$, $\log x = o(x^a)$ as $x \to \infty$.

*Proof.* In each part the right side is positive, so by the theorem on quotients it is enough to show that the quotient tends to $0$.

1. Write $r = 1 + h$ with $h > 0$. For $n \ge k + 1$ the binomial theorem gives $r^n = \sum_j \binom{n}{j} h^j \ge \binom{n}{k+1} h^{k+1}$, since every term is nonnegative. Also $\binom{n}{k+1} = \frac{n(n-1)\cdots(n-k)}{(k+1)!} \ge \frac{(n-k)^{k+1}}{(k+1)!}$. So
$$0 \le \frac{n^k}{r^n} \le \frac{(k+1)!}{h^{k+1}} \left(\frac{n}{n-k}\right)^k \frac{1}{n - k}.$$
As $n \to \infty$, $\frac{n}{n-k} \to 1$ and $\frac{1}{n-k} \to 0$, so the right side tends to $0$.

2. For $x \ge 0$ every term of the series $e^x = \sum_j x^j/j!$ is nonnegative, so $e^x \ge x^{k+1}/(k+1)!$. Then $0 \le x^k/e^x \le (k+1)!/x$ for $x > 0$, which tends to $0$.

3. For $y > 0$, $\log y \le y - 1 < y$, from $e^t \ge 1 + t$ at $t = \log y$. Apply this to $y = x^{a/2}$ with $x > 1$: $\frac{a}{2}\log x < x^{a/2}$. So $0 < \frac{\log x}{x^a} < \frac{2}{a} x^{-a/2}$, and the right side tends to $0$ because $a > 0$. $\square$

::: mathlib
`isLittleO_log_rpow_atTop` · `Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics`

Part 3: `0 < r → Real.log =o[atTop] fun x ↦ x ^ r`, with the real power of Chapter 5. The same file has `isLittleO_pow_exp_pos_mul_atTop` for $x^k = o(e^{bx})$, and `Asymptotics.isLittleO_pow_pow_atTop_of_lt` gives $x^p = o(x^q)$ for $p < q$.

<?decl isLittleO_log_rpow_atTop?>
:::

### Examples

**Example (A polynomial).** Let $u(n) = 3n^2 + 5n$. Then $u(n)/(3n^2) = 1 + \frac{5}{3n} \to 1$, so $u \sim 3n^2$ and $u = \Theta(n^2)$ as $n \to \infty$. Also $u = O(n^3)$, and even $u = o(n^3)$, but $u$ is not $o(n^2)$. In general a polynomial is equivalent at infinity to its term of highest degree: the other terms are $o$ of it, by `Asymptotics.isLittleO_pow_pow_atTop_of_lt`, and part 4 of the rules adds them.

**Counterexample (Sums).** As $n \to \infty$, $n + 1 \sim n$ and $-n \sim -n$. The sums are $1$ and $0$. But $1 \not\sim 0$: the condition $1 - 0 = o(0)$ asks for $|1| \le \varepsilon \cdot 0$ eventually, which is false. A sum of equivalents is safe only when no cancellation occurs, for example when all functions are positive.

### The library around it

The theory is in the folder `Mathlib/Analysis/Asymptotics`. `Defs` has the four definitions, `Basic` has transitivity and the composition with a limit `IsBigO.comp_tendsto`, `Arith` and `Ring` have sums and products, `Lemmas` has the quotients, `Theta` has $\Theta$ and `AsymptoticEquivalent` has $\sim$. The derivative is stated with $o$ in `hasDerivAt_iff_isLittleO`, and the Peano form `taylor_isLittleO` of Chapter 4 is stated with $o$ too.

Common errors of a learner:

- The relation $f = O(g)$ is not an equation: $f_1 = O(g)$ and $f_2 = O(g)$ do not give $f_1 = f_2$.
- In Mathlib, `f =O[l] g` uses norms. For real functions it compares $|f|$ and $|g|$, so $-n^2 = O(n)$ is false, and $-n^2 = O(n^2)$ is true.
- A comparison holds only eventually. $\frac{1}{x} = O(1)$ is true along `atTop` and false along `𝓝[>] 0`.
- $u \sim v$ does not give $u - v \to 0$: $n^2 + n \sim n^2$, but the difference tends to infinity.
- Equivalence is not compatible with sums with cancellation or with $\exp$: $n + 1 \sim n$, but $e^{n+1}/e^n = e \not\to 1$. Use $o$ for the error term and add the errors instead.

### Exercises

1. (A) Prove that $\sqrt{n^2 + n} \sim n$ and that $\sqrt{n^2 + n} - n \to \frac12$ as $n \to \infty$.
2. (A) Prove that $\frac{1}{x} = o(1)$ as $x \to \infty$ and that $\frac{1}{x}$ is not $O(1)$ as $x \to 0^+$.
3. (A) Prove that $f = O(1)$ along $l$ if and only if $f$ is eventually bounded, and that $f = o(1)$ if and only if $f \to 0$.
4. (B) Prove that $\log(n!) \le n \log n$ and $\log(n!) \ge \frac{n}{2}\log\frac{n}{2}$ for $n \ge 2$. Deduce $\log(n!) = \Theta(n \log n)$. Hint: $n! \ge (n/2)^{n/2}$, from the factors $k \ge n/2$.
5. (B) Prove that $2^n = o(n!)$ and $n! = o(n^n)$ as $n \to \infty$. Hint: for the second, $\frac{n!}{n^n} \le \frac{1}{n}$.
6. (B) Prove that $e^u \sim e^v$ along $l$ if and only if $u - v \to 0$ along $l$.
7. (C) Prove that $\sum_{k=1}^{n} \frac1k \sim \log n$. Hint: compare $\frac1k$ with $\int_{k}^{k+1} \frac{dt}{t}$ and with $\int_{k-1}^{k} \frac{dt}{t}$, or use $\log(1 + \frac1k) \le \frac1k \le -\log(1 - \frac1k)$ and sum.

### Notes and history

Paul Bachmann introduced the symbol $O$ in 1894, and Edmund Landau added $o$ in 1909. G. H. Hardy used $\sim$ in *Orders of Infinity* (1910), and Donald Knuth proposed $\Theta$ in 1976. In Mathlib, the asymptotics files were written by Jeremy Avigad and Yury Kudryashov, and the asymptotic equivalence by Anatole Dedecker (2020).

### Reference

<?reference?>
