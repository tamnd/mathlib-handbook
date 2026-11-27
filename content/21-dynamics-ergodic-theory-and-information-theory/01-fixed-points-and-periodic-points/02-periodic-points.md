---
title: Periodic points and the minimal period
kind: theory
modules:
  - Mathlib.Dynamics.PeriodicPts.Defs
  - Mathlib.Dynamics.PeriodicPts.Lemmas
explains:
  E3: [Function.IsPeriodicPt, Function.ptsOfPeriod, Function.periodicPts, Function.minimalPeriod, Function.isPeriodicPt_iff_minimalPeriod_dvd, Function.minimalPeriod_iterate_eq_div_gcd, Function.injective_iff_periodicPts_eq_univ, Function.periodicOrbit, MulAction.period]
  E2: [Function.iterate_mod_minimalPeriod_eq, Function.iterate_injOn_Iio_minimalPeriod, Function.minimalPeriod_eq_zero_of_notMem_periodicPts, Function.minimalPeriod_eq_prime, Function.minimalPeriod_le_card, Function.injective_iff_iterate_factorial_card_eq_id, Function.minimalPeriod_prodMap, Function.Semiconj.mapsTo_periodicPts, Function.Commute.minimalPeriod_of_comp_dvd_lcm, Function.periodicOrbit_length, Function.bijOn_periodicPts, MulAction.pow_smul_eq_iff_period_dvd]
  E1: auto
families: []
requires: [V03, V05, V13]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Periodic points and the minimal period

### Overview

After the fixed points, the next simplest orbits are the ones that close up: $f^{[n]}(x) = x$ for some $n \ge 1$. This section studies such periodic points and the least such $n$, the minimal period. Its main theorem says that the set of periods of a point is the set of multiples of its minimal period. From it follow the minimal period of an iterate, the periods of a product, and the dynamics of a map on a finite set. The order of an element of a group, from Volume 5, Chapter 4, is a special case. The section uses the iterates and the fixed points of Section 1.

### Definitions

**Definition (Periodic point).** Let $f : X \to X$ and $n \in \mathbb{N}$. A point $x$ is *periodic of period $n$* if $f^{[n]}(x) = x$, that is, if $x$ is a fixed point of $f^{[n]}$. The set of such points is $P_n(f)$. A point is *periodic* if it is periodic of some period $n \ge 1$. The set of periodic points is $\mathrm{Per}(f) = \bigcup_{n \ge 1} P_n(f)$.

Each point is periodic of period $0$, and a fixed point is periodic of each period. So $P_n(f)$ is the set of points whose period divides $n$ in the sense below, not the set of points of exact period $n$.

**Definition (Minimal period).** For $x \in \mathrm{Per}(f)$, the *minimal period* $p(x)$ is the least $n \ge 1$ with $f^{[n]}(x) = x$. For $x \notin \mathrm{Per}(f)$, put $p(x) = 0$.

**Definition (Periodic orbit).** For a periodic point $x$ with minimal period $p$, the *periodic orbit* is the cyclic list $(x, f(x), \ldots, f^{[p-1]}(x))$. It is a list up to rotation, because the orbit has no first point.

::: mathlib
`Function.minimalPeriod` · `Mathlib.Dynamics.PeriodicPts.Defs`

`Function.IsPeriodicPt f n x` is `IsFixedPt f^[n] x`. `Function.ptsOfPeriod f n` is `{x | IsPeriodicPt f n x}`, and `Function.periodicPts f` is `{x | ∃ n > 0, IsPeriodicPt f n x}`. `Function.minimalPeriod f x` is `Nat.find` of the existence of a positive period when `x ∈ periodicPts f`, and `0` otherwise. The junk value `0` makes the main theorem below true for all points: `minimalPeriod_eq_zero_of_notMem_periodicPts`. `Function.periodicOrbit f x : Cycle α` is the cycle of the list of the `f^[n] x` for `n < minimalPeriod f x`, and it is `Cycle.nil` for a point that is not periodic.

<?decl Function.minimalPeriod?>
:::

**Definition (Period of an action).** Let a monoid $M$ act on $X$, $m \in M$ and $a \in X$. The *period* of $m$ at $a$ is the minimal period of $a$ for the map $x \mapsto m \cdot x$.

::: mathlib
`MulAction.period` · `Mathlib.Dynamics.PeriodicPts.Lemmas`

`MulAction.period m a` with `MulAction.period_eq_minimalPeriod`; the additive form is `AddAction.period`. The key lemma is `MulAction.pow_smul_eq_iff_period_dvd : m ^ n • a = a ↔ period m a ∣ n`, and for a group the version with `n : ℤ` is `zpow_smul_eq_iff_period_dvd`.

<?decl MulAction.period?>
:::

### Theorems and proofs

**Theorem (Periods are multiples of the minimal period).** For all $x$ and $n$, $f^{[n]}(x) = x$ if and only if $p(x)$ divides $n$.

*Proof.* Suppose first that $x$ is not periodic, so $p(x) = 0$. Then $f^{[n]}(x) = x$ holds only for $n = 0$, and $0$ divides $n$ only for $n = 0$. Now let $p = p(x) \ge 1$. Then $f^{[kp]}(x) = x$ for each $k$, by induction on $k$, because $f^{[(k+1)p]}(x) = f^{[p]}(f^{[kp]}(x))$. Write $n = kp + r$ with $0 \le r < p$. Then
$$f^{[n]}(x) = f^{[r]}(f^{[kp]}(x)) = f^{[r]}(x).$$
If $p \mid n$, then $r = 0$ and $f^{[n]}(x) = x$. If $f^{[n]}(x) = x$, then $f^{[r]}(x) = x$ with $r < p$. By the minimality of $p$, $r$ is not positive, so $r = 0$ and $p \mid n$. $\square$

The proof also shows $f^{[n]}(x) = f^{[n \bmod p]}(x)$.

**Proposition (The orbit has $p$ distinct points).** If $p = p(x) \ge 1$, the points $x, f(x), \ldots, f^{[p-1]}(x)$ are distinct.

*Proof.* Let $f^{[i]}(x) = f^{[j]}(x)$ with $0 \le i < j < p$. Apply $f^{[p-j]}$: $f^{[p-j+i]}(x) = f^{[p]}(x) = x$. But $0 < p - j + i < p$, which contradicts the minimality of $p$. $\square$

::: mathlib
`Function.isPeriodicPt_iff_minimalPeriod_dvd` · `Mathlib.Dynamics.PeriodicPts.Defs`

`IsPeriodicPt f n x ↔ minimalPeriod f x ∣ n`, with no hypothesis on `x`. The remainder form is `iterate_mod_minimalPeriod_eq`, and the distinctness is `iterate_injOn_Iio_minimalPeriod : Set.InjOn (fun n ↦ f^[n] x) (Set.Iio (minimalPeriod f x))`. It gives `periodicOrbit_length` and `nodup_periodicOrbit`. For a prime $p$, `minimalPeriod_eq_prime` says that a point of period $p$ that is not fixed has minimal period $p$.

<?decl Function.isPeriodicPt_iff_minimalPeriod_dvd?>
:::

**Theorem (Minimal period of an iterate).** Let $n \ge 1$ and $p = p(x)$. Then the minimal period of $x$ for $f^{[n]}$ is $p / \gcd(p, n)$.

*Proof.* Put $g = \gcd(p, n)$. For $k \in \mathbb{N}$, $(f^{[n]})^{[k]}(x) = f^{[nk]}(x)$. By the main theorem, this equals $x$ if and only if $p \mid nk$. If $p = 0$, this holds only for $k = 0$, so the minimal period for $f^{[n]}$ is $0 = 0/n$. If $p \ge 1$, then $p \mid nk$ if and only if $(p/g) \mid (n/g)k$. Since $p/g$ and $n/g$ are coprime, this holds if and only if $(p/g) \mid k$. The least positive such $k$ is $p/g$. $\square$

**Theorem (Products).** Let $f : X \to X$ and $g : Y \to Y$. The minimal period of $(x, y)$ for $f \times g$ is $\operatorname{lcm}(p_f(x), p_g(y))$.

*Proof.* $(f \times g)^{[n]}(x, y) = (f^{[n]}(x), g^{[n]}(y))$. By the main theorem, this equals $(x, y)$ if and only if $p_f(x) \mid n$ and $p_g(y) \mid n$, that is, if and only if $\operatorname{lcm}(p_f(x), p_g(y)) \mid n$. Two natural numbers with the same multiples are equal, and the minimal period is characterised by its multiples. This also covers the case where one period is $0$, since $\operatorname{lcm}(0, q) = 0$. $\square$

::: mathlib
`Function.minimalPeriod_iterate_eq_div_gcd` · `Mathlib.Dynamics.PeriodicPts.Defs`

`n ≠ 0 → minimalPeriod f^[n] x = minimalPeriod f x / (minimalPeriod f x).gcd n`. The product rule is `minimalPeriod_prodMap`, and `minimalPeriod_eq_minimalPeriod_iff` is the step "same multiples". For commuting maps, `Commute.minimalPeriod_of_comp_dvd_lcm` says that the minimal period of `f ∘ g` divides the lcm, and `Semiconj.mapsTo_periodicPts` sends periodic points to periodic points.

<?decl Function.minimalPeriod_iterate_eq_div_gcd?>
:::

**Theorem (Maps of a finite set).** Let $X$ be finite with $N$ elements and $f : X \to X$. Then $f$ is injective if and only if each point is periodic. In this case $p(x) \le N$ for each $x$, and $f^{[N!]} = \mathrm{id}$.

*Proof.* Let $f$ be injective and $x \in X$. The $N + 1$ points $f^{[0]}(x), \ldots, f^{[N]}(x)$ are not distinct, so $f^{[i]}(x) = f^{[j]}(x)$ for some $i < j$. The map $f^{[i]}$ is injective, and $f^{[i]}(f^{[j-i]}(x)) = f^{[i]}(x)$, so $f^{[j-i]}(x) = x$ with $j - i \ge 1$. Conversely, let each point be periodic and $f(x) = f(y)$. Put $m = p(x)p(y) \ge 1$. Then $f^{[m]}(x) = x$ and $f^{[m]}(y) = y$, and
$$x = f^{[m-1]}(f(x)) = f^{[m-1]}(f(y)) = y.$$
For the bound, the $p(x)$ points of the orbit of $x$ are distinct, so $p(x) \le N$. Then $p(x) \mid N!$, and $f^{[N!]}(x) = x$ by the main theorem. $\square$

::: mathlib
`Function.injective_iff_periodicPts_eq_univ` · `Mathlib.Dynamics.PeriodicPts.Lemmas`

`[Finite α] → (Injective f ↔ periodicPts f = Set.univ)`. With `[Fintype α]` the file has `minimalPeriod_le_card` and `injective_iff_iterate_factorial_card_eq_id : Injective f ↔ f^[(Fintype.card α).factorial] = id`. On any set, `bijOn_periodicPts` says that `f` permutes its periodic points.

<?decl Function.injective_iff_periodicPts_eq_univ?>
:::

### Examples

**Example (The doubling map).** Let $D(x) = 2x \bmod 1$ on $\mathbb{R}/\mathbb{Z}$. Then $D^{[n]}(x) = 2^n x$, and $D^{[n]}(x) = x$ means $(2^n - 1)x \in \mathbb{Z}$. So $P_n(D)$ is the set of the $2^n - 1$ points $k/(2^n - 1)$, $0 \le k < 2^n - 1$. The number $e_n$ of points of minimal period exactly $n$ satisfies $\sum_{d \mid n} e_d = 2^n - 1$, by the main theorem. This gives $e_1 = 1$, $e_2 = 2$, $e_3 = 6$, $e_4 = 15 - 3 = 12$ and $e_6 = 63 - 1 - 2 - 6 = 54$. For instance $1/7 \mapsto 2/7 \mapsto 4/7 \mapsto 1/7$ is an orbit of minimal period $3$. The point $1/3$ has minimal period $2$ for $D$, and for $D^{[2]}$ the formula gives $2/\gcd(2, 2) = 1$: it is a fixed point of $D^{[2]}$.

**Example (The order of an element).** Let $G$ be a monoid and $a \in G$. Mathlib defines $\operatorname{ord}(a)$ as the minimal period of $1$ for the map $x \mapsto ax$, with the value $0$ for infinite order. The main theorem becomes $a^n = 1 \iff \operatorname{ord}(a) \mid n$, which is `orderOf_dvd_iff_pow_eq_one`. The theorem on iterates becomes $\operatorname{ord}(a^n) = \operatorname{ord}(a)/\gcd(\operatorname{ord}(a), n)$ for $n \ne 0$, which is `orderOf_pow'`.

**Example (A permutation).** Let $\sigma = (1\,2\,3)(4\,5)$ on $\{1, \ldots, 5\}$. The points $1, 2, 3$ have minimal period $3$ and the points $4, 5$ have minimal period $2$. The orbit of $1$ is the cycle $(1, 2, 3)$, the same cycle as $(2, 3, 1)$. In $\{1, \ldots, 5\}^2$ the point $(1, 4)$ has minimal period $\operatorname{lcm}(3, 2) = 6$ for $\sigma \times \sigma$. The theorem on finite sets gives $\sigma^{120} = \mathrm{id}$; the true order is $6$.

### The library around it

Common errors of a learner:

- `IsPeriodicPt f 0 x` is always true, and `ptsOfPeriod f n` contains the points whose minimal period divides `n`. A point of exact period `n` is a point with `minimalPeriod f x = n`.
- `minimalPeriod f x = 0` means that `x` is not periodic. Lemmas on periodic points often ask for `x ∈ periodicPts f` or for `0 < minimalPeriod f x` (`minimalPeriod_pos_iff_mem_periodicPts`).

### Exercises

1. (A) Show that $P_m(f) \cap P_n(f) = P_{\gcd(m, n)}(f)$.
2. (A) Find all periodic points of $x \mapsto -x$ on $\mathbb{R}$ and of $x \mapsto x^3$ on $\mathbb{R}$, with their minimal periods.
3. (A) Show that if $x$ is periodic, then $f(x)$ is periodic with the same minimal period.
4. (B) Let $T(x) = 3x \bmod 1$ on $\mathbb{R}/\mathbb{Z}$. Count the points of minimal period exactly $n$ for $n \le 4$.
5. (B) Let $f$ be continuous on $\mathbb{R}$ with a point of minimal period $2$. Show that $f$ has a fixed point. Hint: apply the intermediate value theorem to $f(x) - x$ on the orbit.
6. (B) Give a map of $\mathbb{N}$ that is injective and has no periodic point, and a surjective map of $\mathbb{N}$ whose periodic points are not all points.
7. (C) Let $f$ and $g$ commute, with coprime minimal periods $p, q$ at $x$. Show that the minimal period of $x$ for $f \circ g$ is $pq$.

### Notes and history

The count of the points of exact period from the numbers $2^n - 1$ is a Möbius inversion. Sharkovskii's theorem of 1964 orders the possible minimal periods of a continuous map of an interval, and its first case is Exercise 5. The index of this edition has no declaration for Sharkovskii's theorem.

### Reference

<?reference?>
