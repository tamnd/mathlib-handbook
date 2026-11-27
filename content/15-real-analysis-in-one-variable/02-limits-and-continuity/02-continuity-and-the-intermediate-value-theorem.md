---
title: Continuity and the intermediate value theorem
kind: theory
modules:
  - Mathlib.Analysis.Real.Sqrt
explains:
  E3: [Real.sqrt]
  E2: [NNReal.sqrt, Real.sq_sqrt, Real.sqrt_sq, Real.continuous_sqrt, Real.sqrt_le_sqrt, Real.sqrt_lt_sqrt, Real.sqrt_mul_self_eq_abs, Real.sqrt_two_lt_three_halves]
  E1: auto
families: []
requires: [V02, V13, V15.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Continuity and the intermediate value theorem

### Overview

A function is continuous at a point when its limit there is its value. Sums, products, quotients and compositions of continuous functions are continuous. The first deep theorem about continuous functions is the intermediate value theorem: a continuous function on an interval takes every value between two of its values. Its proof uses the least upper bound.

The section deduces four consequences: the existence of $n$-th roots, a real root for each polynomial of odd degree, the strict monotonicity of a continuous injective function on an interval, and the continuity of its inverse. The square root `Real.sqrt` of Mathlib is the main example.

### Definitions

**Definition (Continuity).** Let $f : D \to \mathbb{R}$ and $a \in D$. The function $f$ is *continuous at* $a$ if for every $\varepsilon > 0$ there is $\delta > 0$ such that $|f(x) - f(a)| < \varepsilon$ for all $x \in D$ with $|x - a| < \delta$. It is *continuous on* $D$ if it is continuous at each point of $D$.

Remarks. If $a$ is an accumulation point of $D$, continuity at $a$ means $\lim_{x \to a} f(x) = f(a)$. At an isolated point of $D$ every function is continuous. By the sequential characterization, $f$ is continuous at $a$ if and only if $f(x_n) \to f(a)$ for every sequence $x_n \to a$ in $D$.

::: mathlib
`ContinuousAt` · `Mathlib.Topology.Defs.Filter`

`ContinuousAt f a` is `Tendsto f (𝓝 a) (𝓝 (f a))`. `ContinuousWithinAt f s a` uses `𝓝[s] a`. `ContinuousOn f s` is `∀ x ∈ s, ContinuousWithinAt f s x`, the textbook continuity on $D = s$. `Continuous f` says that preimages of open sets are open, and `continuous_iff_continuousAt` says that it is continuity at every point. A textbook function $f : [a, b] \to \mathbb{R}$ is a function `f : ℝ → ℝ` with `ContinuousOn f (Set.Icc a b)`.

<?decl ContinuousAt?>
:::

**Definition (Interval).** A set $I \subseteq \mathbb{R}$ is an *interval* if $x, y \in I$ and $x < z < y$ give $z \in I$. Mathlib calls this property `Set.OrdConnected`.

### Theorems and proofs

**Theorem (Operations).** If $f$ and $g$ are continuous at $a$, then so are $f + g$ and $f g$, and so is $f/g$ if $g(a) \ne 0$. If $f$ is continuous at $a$ and $h$ is continuous at $f(a)$, then $h \circ f$ is continuous at $a$.

*Proof.* For the operations, the proofs of the algebra of limits apply with $L = f(a)$, $M = g(a)$ and the condition $|x - a| < \delta$. For the composition let $\varepsilon > 0$. Choose $\eta$ with $|h(y) - h(f(a))| < \varepsilon$ for $|y - f(a)| < \eta$, and $\delta$ with $|f(x) - f(a)| < \eta$ for $|x - a| < \delta$. Then $|h(f(x)) - h(f(a))| < \varepsilon$ for $|x - a| < \delta$. $\square$

So every polynomial is continuous on $\mathbb{R}$. In Mathlib the lemmas are `Continuous.add`, `Continuous.mul`, `Continuous.div`, `Continuous.comp` and `Polynomial.continuous`, and the tactic `fun_prop` chains them.

**Theorem (Intermediate value theorem).** Let $a \le b$ and let $f$ be continuous on $[a, b]$. For every $y$ between $f(a)$ and $f(b)$ there is $c \in [a, b]$ with $f(c) = y$.

*Proof.* Assume first $f(a) \le y \le f(b)$. Let $S = \{ x \in [a, b] : f(x) \le y \}$. It contains $a$ and is bounded above by $b$, so it has a least upper bound $c = \sup S$, with $a \le c \le b$.

Step 1: $f(c) \le y$. For each $n \ge 1$ the number $c - 1/n$ is not an upper bound of $S$, so there is $x_n \in S$ with $c - 1/n < x_n \le c$. Then $x_n \to c$, so $f(x_n) \to f(c)$ by continuity. Each $f(x_n) \le y$, and a limit of numbers $\le y$ is $\le y$ (Chapter 1). So $f(c) \le y$.

Step 2: $f(c) \ge y$. If $c = b$, then $f(c) = f(b) \ge y$. If $c < b$, let $x_n = \min(c + 1/n, b)$. Then $x_n \in [a, b]$ and $x_n > c = \sup S$, so $x_n \notin S$ and $f(x_n) > y$. Also $x_n \to c$, so $f(c) = \lim f(x_n) \ge y$.

So $f(c) = y$. If instead $f(b) \le y \le f(a)$, apply the first case to $-f$ and $-y$. $\square$

**Corollary (Images of intervals).** If $I$ is an interval and $f$ is continuous on $I$, then $f(I)$ is an interval.

*Proof.* Let $f(x) < w < f(x')$ with $x, x' \in I$. The closed interval between $x$ and $x'$ lies in $I$, and the theorem on it gives $c$ with $f(c) = w$. $\square$

::: mathlib
`intermediate_value_Icc` · `Mathlib.Topology.Order.IntermediateValue`

The form `a ≤ b → ContinuousOn f (Set.Icc a b) → Set.Icc (f a) (f b) ⊆ f '' Set.Icc a b`. The case $f(b) \le y \le f(a)$ is `intermediate_value_Icc'`, and `intermediate_value_uIcc` covers both. The domain is any conditionally complete, densely ordered linear order with the order topology. The general statement behind the corollary is `IsPreconnected.intermediate_value`.

<?decl intermediate_value_Icc?>
:::

**Theorem (Roots).** Let $n \ge 1$ and $y \ge 0$. There is exactly one $x \ge 0$ with $x^n = y$.

*Proof.* Existence: $f(x) = x^n$ is continuous on $[0, 1 + y]$, with $f(0) = 0 \le y$ and $f(1 + y) = (1 + y)^n \ge 1 + y > y$. The intermediate value theorem gives the root. Uniqueness: for $0 \le x < x'$, induction on $n$ gives $x^n < x'^n$, so $x \mapsto x^n$ is injective on $[0, \infty)$. $\square$

**Definition (Square root in Mathlib).** For $y \ge 0$, $\sqrt{y}$ is the unique $x \ge 0$ with $x^2 = y$. For $y < 0$, Mathlib sets $\sqrt{y} = 0$.

::: mathlib
`Real.sqrt` · `Mathlib.Analysis.Real.Sqrt`

`Real.sqrt x = NNReal.sqrt (Real.toNNReal x)`, with the notation `√x`. Since `Real.toNNReal` sends a negative number to `0`, `√(-4) = 0`. This junk value makes `Real.sqrt` total and continuous on all of `ℝ`: `Real.continuous_sqrt`. Many lemmas need `0 ≤ x`: `Real.sq_sqrt : 0 ≤ x → √x ^ 2 = x` and `Real.sqrt_sq : 0 ≤ x → √(x ^ 2) = x`, while `Real.sqrt_mul_self_eq_abs` gives `√(x * x) = |x|` for every `x`. The notation binds tightly: `√x⁻¹` is `√(x⁻¹)`.

<?decl Real.sqrt?>
:::

::: mathlib
`NNReal.sqrt` · `Mathlib.Analysis.Real.Sqrt`

On `ℝ≥0` the square root is an order isomorphism `ℝ≥0 ≃o ℝ≥0`, the inverse of $x \mapsto x^2$. Existence and uniqueness of roots are the surjectivity and injectivity of that map. An order isomorphism is continuous by `OrderIso.continuous`, which is the last theorem of this section in Mathlib form.

<?decl NNReal.sqrt?>
:::

**Theorem (Odd degree).** Let $p(x) = x^d + a_{d-1} x^{d-1} + \dots + a_0$ with $d$ odd. Then $p$ has a real root.

*Proof.* Let $M = 1 + |a_0| + \dots + |a_{d-1}|$, and $|x| \ge M$. Then $|x| \ge 1$, so $|x|^i \le |x|^{d-1}$ for $i \le d - 1$, and
$$|a_{d-1} x^{d-1} + \dots + a_0| \le (M - 1)|x|^{d-1} < M |x|^{d-1} \le |x|^d.$$
So $p(x)$ has the sign of $x^d$, which is the sign of $x$ since $d$ is odd. Thus $p(-M) < 0 < p(M)$, and the intermediate value theorem on $[-M, M]$ gives a root. $\square$

**Theorem (Continuous injective functions).** Let $I$ be an interval and $f : I \to \mathbb{R}$ continuous and injective. Then $f$ is strictly increasing or strictly decreasing on $I$.

*Proof.* Step 1: $I = [a, b]$ with $a < b$. Then $f(a) \ne f(b)$; assume $f(a) < f(b)$, the other case follows with $-f$. Claim: $f(a) < f(x) < f(b)$ for $x \in (a, b)$. If $f(x) < f(a)$, the intermediate value theorem on $[x, b]$ gives $c \in (x, b)$ with $f(c) = f(a)$, and $c \ne a$ contradicts injectivity. If $f(x) > f(b)$, the theorem on $[a, x]$ gives $c \in (a, x)$ with $f(c) = f(b)$, again a contradiction. Now let $a \le x < y \le b$. Then $f(x) < f(b)$, by assumption or by the claim, so the claim applies on $[x, b]$ and gives $f(x) < f(y)$ when $y < b$. For $y = b$ this is $f(x) < f(b)$.

Step 2: a general $I$ with two points $a < b$ and $f(a) < f(b)$. For $x < y$ in $I$, let $u = \min(a, x)$ and $v = \max(b, y)$. Then $[u, v] \subseteq I$, and by Step 1 $f$ is strictly monotone on $[u, v]$. Since $f(a) < f(b)$, it is increasing, so $f(x) < f(y)$. $\square$

In Mathlib the closed interval case is `ContinuousOn.strictMonoOn_of_injOn_Icc'`, and the case of all of `ℝ` is `Continuous.strictMono_of_inj`.

**Theorem (Continuity of the inverse).** Let $I$ be an interval and $f : I \to \mathbb{R}$ continuous and strictly increasing. Then $J = f(I)$ is an interval, and $g = f^{-1} : J \to I$ is continuous and strictly increasing.

*Proof.* $J$ is an interval by the corollary, and $g$ exists since $f$ is injective. If $y < y'$ and $g(y) \ge g(y')$, then $y \ge y'$, a contradiction, so $g$ is increasing. Let $y_0 \in J$, $x_0 = g(y_0)$ and $\varepsilon > 0$. If $I$ has a point larger than $x_0$, it contains some $x_1$ with $x_0 < x_1 < x_0 + \varepsilon$. Put $\delta_1 = f(x_1) - y_0 > 0$. For $y \in J$ with $y < y_0 + \delta_1 = f(x_1)$, the monotonicity of $g$ gives $g(y) < x_1 < x_0 + \varepsilon$. If $x_0$ is the right end of $I$, then $g(y) \le x_0$ for all $y$, and $\delta_1 = 1$ works. In the same way there is $\delta_2$ with $g(y) > x_0 - \varepsilon$ for $y > y_0 - \delta_2$. With $\delta = \min(\delta_1, \delta_2)$, $|y - y_0| < \delta$ gives $|g(y) - x_0| < \varepsilon$. $\square$

::: mathlib
`OrderIso.continuous` · `Mathlib.Topology.Order.MonotoneContinuity`

An order isomorphism between two order topologies is continuous, and so is its inverse. The general form of the proof above is `Monotone.continuous_of_surjective`: a monotone map onto a densely ordered target is continuous.

<?decl OrderIso.continuous?>
:::

### Examples

**Example (Bisection for $x^5 - x - 1$).** Let $p(x) = x^5 - x - 1$. Then $p(1) = -1$ and $p(2) = 29$. Halve the interval and keep the half with a sign change:

| interval | midpoint $m$ | $p(m)$ |
|---|---|---|
| $[1, 2]$ | $1.5$ | $5.0938$ |
| $[1, 1.5]$ | $1.25$ | $0.8018$ |
| $[1, 1.25]$ | $1.125$ | $-0.3230$ |
| $[1.125, 1.25]$ | $1.1875$ | $0.1739$ |

So a root lies in $(1.125, 1.1875)$. After $k$ steps the interval has length $2^{-k}$. The root is near $1.1673$. For $\sqrt{2}$ the same idea gives $1.4^2 = 1.96 < 2 < 2.0164 = 1.42^2$, so $1.4 < \sqrt{2} < 1.42$. Mathlib has `Real.sqrt_two_lt_three_halves : √2 < 3 / 2`.

**Counterexample (The theorem fails over $\mathbb{Q}$).** Let $f(x) = x^2 - 2$ on $\{x \in \mathbb{Q} : 0 \le x \le 2\}$. It is continuous, and $f(0) = -2 < 0 < 2 = f(2)$. But $x^2 = 2$ has no rational solution (Volume 2). The proof breaks at the supremum: $\{x \in \mathbb{Q} \cap [0, 2] : x^2 \le 2\}$ has no least upper bound in $\mathbb{Q}$. In Mathlib, `intermediate_value_Icc` needs a `ConditionallyCompleteLinearOrder`, and `ℚ` has no such instance.

**Counterexample (Continuity is needed).** Let $f = \mathbf{1}_{[1, \infty)}$ on $[0, 2]$. Then $f(0) = 0$ and $f(2) = 1$, but $f$ never takes the value $1/2$.

### The library around it

The intermediate value theorem and its variants are in `Mathlib.Topology.Order.IntermediateValue`, for example `intermediate_value_Ioo` and `ContinuousOn.surjOn_Icc`. The file `Mathlib.Analysis.Real.Sqrt` has the order lemmas of the square root, each with the hypothesis that makes it true: `Real.sqrt_le_sqrt` (none), `Real.sqrt_lt_sqrt` (`0 ≤ x`), `Real.sqrt_lt'` (`0 < y`), `Real.lt_sqrt` (`0 ≤ x`).

Common errors of a learner:

- Using `Real.sq_sqrt` without `0 ≤ x`. For `x = -1` the left side is `√(-1) ^ 2 = 0`.
- Stating continuity on $[a, b]$ as `Continuous f`. The right form is `ContinuousOn f (Set.Icc a b)`.
- Reading uniqueness into the intermediate value theorem. It gives existence only.
- Applying the theorem on `ℚ` or `ℤ`. The domain must be complete and densely ordered.

The reference table at the end of the section lists the declarations of this section.

### Exercises

1. (A) Show that $x^3 - 3x + 1$ has three real roots. Hint: compute the signs at $-2, -1, 0, 1, 2$.
2. (A) Let $f : [0, 1] \to [0, 1]$ be continuous. Prove that $f$ has a fixed point. Hint: consider $f(x) - x$.
3. (A) Prove $\sqrt{x y} = \sqrt{x} \sqrt{y}$ for $x, y \ge 0$ from the uniqueness of roots, and show that it fails for $x = y = -1$ in Mathlib.
4. (B) Prove that a continuous $f : \mathbb{R} \to \mathbb{R}$ with only rational values is constant.
5. (B) Show that no continuous $f : \mathbb{R} \to \mathbb{R}$ takes each value exactly twice.
6. (C) Prove the intermediate value theorem by bisection, with nested intervals $[a_k, b_k]$ such that $f(a_k) \le y \le f(b_k)$. Hint: use the nested interval property from Chapter 1.

### Notes and history

Bolzano proved the intermediate value theorem in 1817 with a form of the least upper bound principle that had no foundation yet. Cauchy gave the bisection proof in 1821. The constructions of $\mathbb{R}$ by Dedekind and Cantor in 1872 supplied the foundation. Rudin, *Principles of Mathematical Analysis*, Chapter 4, deduces the theorem from connectedness.

### Reference

<?reference?>
