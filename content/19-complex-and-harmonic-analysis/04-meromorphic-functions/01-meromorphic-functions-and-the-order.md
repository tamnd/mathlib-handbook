---
title: Meromorphic functions and the order
kind: theory
modules:
  - Mathlib.Analysis.Meromorphic.Basic
  - Mathlib.Analysis.Meromorphic.Order
  - Mathlib.Analysis.Meromorphic.IsolatedZeros
  - Mathlib.Analysis.Meromorphic.NormalForm
  - Mathlib.Analysis.Meromorphic.RCLike
explains:
  E3: [MeromorphicAt, meromorphicOrderAt, meromorphicOrderAt_eq_int_iff, meromorphicOrderAt_mul, MeromorphicOn.isClopen_setOfPred_meromorphicOrderAt_eq_top, MeromorphicNFAt]
  E2: [MeromorphicOn, Meromorphic, MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero, meromorphicOrderAt_eq_top_iff, meromorphicOrderAt_inv, meromorphicOrderAt_add, meromorphicOrderAt_add_of_ne, meromorphicOrderAt_of_not_meromorphicAt, meromorphicOrderAt_id_sub_const, tendsto_zero_iff_meromorphicOrderAt_pos, tendsto_cobounded_iff_meromorphicOrderAt_neg, tendsto_nhds_iff_meromorphicOrderAt_nonneg, MeromorphicAt.analyticAt, MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall, MeromorphicOn.codiscreteWithin_setOfPred_ne_zero, MeromorphicNFOn, toMeromorphicNFAt, meromorphicNFAt_iff_analyticAt_or]
  E1: auto
families: []
requires: [V17.C07, V19.C02, V19.C03, V13]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Meromorphic functions and the order

### Overview

The functions $1/z$, $\tan z$ and $1/\sin z$ are holomorphic except at isolated points, where they behave like a negative power of $z - z_0$. Such a point is a pole, and a function whose only singularities are poles is meromorphic. Each point has an order in $\mathbb{Z} \cup \{\infty\}$: the exponent $n$ in $f(z) = (z - z_0)^n g(z)$ with $g(z_0) \ne 0$. The section proves that the order is additive, reads it from the size of $f$, proves that zeros and poles on a connected set are isolated, and defines the normal form.

The field $\mathbb{K}$ is nontrivially normed (Volume 17, Chapter 7) and values lie in a normed space $E$. For $\mathbb{K} = \mathbb{C}$, analytic means holomorphic near the point (Chapter 2, Section 3).

### Definitions

A statement holds off $x$ near $x$ when it holds on $B(x, r) \setminus \{x\}$ for some $r > 0$.

**Definition (Meromorphic function).** A function $f : \mathbb{K} \to E$ is meromorphic at $x$ when $z \mapsto (z - x)^n f(z)$ is analytic at $x$ for some $n \in \mathbb{N}$. It is meromorphic on $U$ when it is meromorphic at each point of $U$.

The value $f(x)$ does not matter: if $f_1 = f$ off $x$, then $(z - x)^{n + 1} f_1(z) = (z - x)^{n + 1} f(z)$ for all $z$.

**Definition (Order).** Let $f$ be meromorphic at $x$. The order $\operatorname{ord}_x f$ is $\infty$ when $f = 0$ off $x$ near $x$. Otherwise it is the unique $n \in \mathbb{Z}$ with $f(z) = (z - x)^n g(z)$ off $x$ near $x$, where $g$ is analytic at $x$ and $g(x) \ne 0$.

The point $x$ is a zero of order $n$ when $\operatorname{ord}_x f = n > 0$, and a pole of order $-n$ when $n < 0$. The factorization theorem shows that the order exists.

**Definition (Normal form).** A function $f$ is in normal form at $x$ when it is analytic at $x$, or when it is meromorphic at $x$ with $\operatorname{ord}_x f < 0$ and $f(x) = 0$.

### Theorems and proofs

**Theorem (Factorization).** Let $f$ be meromorphic at $x$. Then either $f = 0$ off $x$ near $x$, or $f(z) = (z - x)^n g(z)$ off $x$ near $x$ for a unique $n \in \mathbb{Z}$ and some $g$ analytic at $x$ with $g(x) \ne 0$. In the second case $f \ne 0$ off $x$ near $x$.

*Proof.* Choose $m$ with $h(z) = (z - x)^m f(z)$ analytic at $x$. By the isolated zeros theorem of Volume 17, Chapter 7, either $h = 0$ near $x$, or $h(z) = (z - x)^k g(z)$ near $x$ with $k \in \mathbb{N}$ and $g(x) \ne 0$. For $z \ne x$, $f(z) = (z - x)^{-m} h(z)$. So $f = 0$ off $x$ in the first case, and $f(z) = (z - x)^{k - m} g(z)$ off $x$ in the second.

By continuity $g \ne 0$ on a ball around $x$, so $f \ne 0$ off $x$ on this ball. Every punctured ball contains points, since the absolute value is nontrivial, so the cases exclude each other.

For uniqueness, let $(z - x)^n g(z) = (z - x)^p h(z)$ off $x$, with $g(x), h(x) \ne 0$ and $n < p$. Then $g(z) = (z - x)^{p - n} h(z)$ off $x$, and continuity at $x$ gives $g(x) = 0$, a contradiction. $\square$

::: mathlib
`MeromorphicAt` · `Mathlib.Analysis.Meromorphic.Basic`

`MeromorphicAt f x` is `∃ n : ℕ, AnalyticAt 𝕜 (fun z ↦ (z - x) ^ n • f z) x`. `MeromorphicOn f U` and `Meromorphic f` ask it on `U` and everywhere. The dichotomy above is `MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero`.

<?decl MeromorphicAt?>
:::

::: mathlib
`meromorphicOrderAt` · `Mathlib.Analysis.Meromorphic.Order`

`meromorphicOrderAt f x : WithTop ℤ`, with the junk value `0` if `f` is not meromorphic at `x` (`meromorphicOrderAt_of_not_meromorphicAt`). `meromorphicOrderAt_eq_int_iff` is the definition above, with `∀ᶠ z in 𝓝[≠] x` for "off $x$ near $x$", and `meromorphicOrderAt_eq_top_iff` describes `⊤`.

<?decl meromorphicOrderAt?>
<?decl meromorphicOrderAt_eq_int_iff?>
:::

**Theorem (Order of a product).** Let $f, g : \mathbb{K} \to \mathbb{K}$ be meromorphic at $x$. Then $\operatorname{ord}_x (fg) = \operatorname{ord}_x f + \operatorname{ord}_x g$, with $n + \infty = \infty$, and $\operatorname{ord}_x (1/f) = -\operatorname{ord}_x f$ when the order of $f$ is finite.

*Proof.* If $f$ or $g$ is $0$ off $x$, so is $fg$, and both sides are $\infty$. Otherwise $f = (z - x)^n u$ and $g = (z - x)^p v$ off $x$, with $u(x) v(x) \ne 0$. Then $fg = (z - x)^{n + p} uv$ with $(uv)(x) \ne 0$, so the order is $n + p$ by uniqueness. Also $1/f = (z - x)^{-n} (1/u)$, and $1/u$ is analytic at $x$ since $u(x) \ne 0$. $\square$

::: mathlib
`meromorphicOrderAt_mul` · `Mathlib.Analysis.Meromorphic.Order`

The sum is in `WithTop ℤ`, where `⊤ + n = ⊤`, so there is no case split. `meromorphicOrderAt_inv` needs no hypothesis, since `-⊤ = ⊤`.

<?decl meromorphicOrderAt_mul?>
:::

**Theorem (Order and limits).** Let $f$ be meromorphic at $x$, and let $z \to x$ with $z \ne x$. Then $f(z) \to 0$ if and only if $\operatorname{ord}_x f > 0$, $\|f(z)\| \to \infty$ if and only if $\operatorname{ord}_x f < 0$, and $f(z)$ has a limit if and only if $\operatorname{ord}_x f \ge 0$.

*Proof.* For the order $\infty$, $f \to 0$. Otherwise $\|f(z)\| = |z - x|^n \|g(z)\|$ with $\|g(z)\| \to \|g(x)\| > 0$. This tends to $0$ for $n > 0$ and to $\infty$ for $n < 0$, and $f = g \to g(x) \ne 0$ for $n = 0$. The three behaviours differ, so each fixes the sign of $n$. $\square$

So a function with $\operatorname{ord}_x f \ge 0$ becomes analytic at $x$ when its value there is the limit, as in Chapter 3, Section 3.

**Theorem (Isolated zeros and poles).** Let $U \subseteq \mathbb{K}$ be connected and $f$ meromorphic on $U$. Then either $\operatorname{ord}_u f = \infty$ for all $u \in U$, or $\operatorname{ord}_u f \ne \infty$ for all $u \in U$. In the second case each $u \in U$ has a punctured neighbourhood on which $f \ne 0$.

*Proof.* Let $S = \{u \in U : \operatorname{ord}_u f = \infty\}$.

Step 1: $S$ is open in $U$. For $u \in S$ there is $r > 0$ with $f = 0$ on $B(u, r) \setminus \{u\}$. A point $y \ne u$ of $U \cap B(u, r)$ has a ball around it in this set, so $y \in S$.

Step 2: $U \setminus S$ is open in $U$. For $u \notin S$ the factorization gives $r > 0$ with $f \ne 0$ on $B(u, r) \setminus \{u\}$. For $y \ne u$ in $U \cap B(u, r)$, every punctured ball around $y$ meets this set, so $y \notin S$.

Step 3: the clopen subset $S$ of the connected set $U$ is $\emptyset$ or $U$ (Volume 13). If $S = \emptyset$, the factorization gives the punctured neighbourhoods. $\square$

In the second case a compact subset of $U$ contains only finitely many zeros and poles.

::: mathlib
`MeromorphicOn.isClopen_setOfPred_meromorphicOrderAt_eq_top` · `Mathlib.Analysis.Meromorphic.Order`

The set `{u : U | meromorphicOrderAt f u = ⊤}` is clopen: Steps 1 and 2. Step 3 is `MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall`. With no order `⊤`, `MeromorphicOn.codiscreteWithin_setOfPred_ne_zero` gives `f x ≠ 0` for `x` in the filter `Filter.codiscreteWithin U`.

<?decl MeromorphicOn.isClopen_setOfPred_meromorphicOrderAt_eq_top?>
:::

**Theorem (Normal form).** Let $f$ be meromorphic at $x$. Let $\tilde f = f$ off $x$, with $\tilde f(x)$ the limit of $f$ when $\operatorname{ord}_x f \ge 0$ and $\tilde f(x) = 0$ when $\operatorname{ord}_x f < 0$. Then $\tilde f$ is in normal form at $x$.

*Proof.* $\tilde f$ is meromorphic with the same order, since neither notion uses the value at $x$. A negative order gives normal form by definition. For the order $\infty$, $\tilde f = 0$ near $x$. For an order $n \ge 0$, $\tilde f = (z - x)^n g$ off $x$, and $\tilde f(x) = \lim (z - x)^n g(z) = 0^n g(x)$, so $\tilde f = (z - x)^n g$ on a full neighbourhood. In both cases $\tilde f$ is analytic at $x$. $\square$

::: mathlib
`MeromorphicNFAt` · `Mathlib.Analysis.Meromorphic.NormalForm`

`MeromorphicNFAt f x` says that `f` is `0` near `x`, or `(· - x) ^ n • g` on a full neighbourhood with `g x ≠ 0`. For `n < 0`, `0 ^ n = 0` in Lean, the value at a pole. The equivalence with the definition above is `meromorphicNFAt_iff_analyticAt_or`, and $\tilde f$ is `toMeromorphicNFAt f x`. `MeromorphicNFOn f U` asks it on `U`.

<?decl MeromorphicNFAt?>
:::

### Examples

**Example (The tangent).** The zeros $z_k = \pi/2 + k\pi$ of $\cos$ are simple, since $\cos'(z_k) = -\sin z_k \ne 0$. By the product theorem $\operatorname{ord}_{z_k} \tan = 0 - 1 = -1$, a simple pole. At $k\pi$ the order is $1 - 0 = 1$, and elsewhere it is $0$.

**Example (Poles that accumulate).** The function $1/\sin(1/z)$ is meromorphic on $\mathbb{C} \setminus \{0\}$ with simple poles at $1/(k\pi)$, $k \ne 0$. They accumulate at $0$. The function is not meromorphic at $0$: by the factorization theorem it would be finite on some punctured ball around $0$, and each such ball contains poles.

### The library around it

The order of $z - x$ is $1$ by `meromorphicOrderAt_id_sub_const`. The limit theorem is `tendsto_zero_iff_meromorphicOrderAt_pos`, `tendsto_cobounded_iff_meromorphicOrderAt_neg` and `tendsto_nhds_iff_meromorphicOrderAt_nonneg`. A meromorphic function continuous at $x$ is analytic there by `MeromorphicAt.analyticAt`. Exercise 4 is `meromorphicOrderAt_add` and `meromorphicOrderAt_add_of_ne`.

Common errors of a learner:

- Using a theorem on `meromorphicOrderAt` without `MeromorphicAt f x`. The junk value makes the statement false.
- Treating a meromorphic function as a map to the Riemann sphere. In Mathlib it is a map `𝕜 → E`, with an arbitrary value at a pole.

### Exercises

1. (A) Compute the order of $z^2/(1 - \cos z)$ at $0$ and of $1/(e^z - 1)$ at $2\pi i$. Hint: expand the denominators to the first nonzero term.
2. (B) Let $f$ be meromorphic at $x$ with order $n \ne 0, \infty$. Show that $\operatorname{ord}_x f' = n - 1$. Hint: differentiate $(z - x)^n g(z)$. Explain what fails when $n = 0$.
3. (B) Show that $e^{1/z}$ is not meromorphic at $0$. Hint: let $z \to 0$ along the two halves of the real axis and use the theorem on order and limits.
4. (B) Show that $\operatorname{ord}_x (f + g) \ge \min(\operatorname{ord}_x f, \operatorname{ord}_x g)$, with equality when the orders differ, and give an example where it is strict. Hint: for $n \le p$, write $f + g = (z - x)^n (u + (z - x)^{p - n} v)$.
5. (C) Let $f$ be meromorphic on $\mathbb{C}$ with $|f(z)| \to \infty$ as $|z| \to \infty$. Show that $f$ has finitely many zeros and poles and is a rational function. Hint: remove the poles with a polynomial and use Chapter 3, Section 1.

### Notes and history

"Meromorphic" means "of fractional form": locally such a function is a quotient of two holomorphic functions.

### Reference

<?reference?>
