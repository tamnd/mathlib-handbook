---
title: The translation number
kind: theory
modules:
  - Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber
explains:
  E3: [CircleDeg1Lift.translationNumber, CircleDeg1Lift.tendsto_translationNumber, CircleDeg1Lift.dist_pow_map_zero_mul_translationNumber_le, CircleDeg1Lift.translationNumber_eq_of_semiconj, CircleDeg1Lift.exists_eq_add_translationNumber, CircleDeg1Lift.translationNumber_eq_rat_iff, CircleDeg1Lift.semiconj_of_group_action_of_forall_translationNumber_eq]
  E2: [CircleDeg1Lift.transnumAuxSeq, CircleDeg1Lift.transnumAuxSeq_dist_lt, CircleDeg1Lift.translationNumber_eq_of_tendsto₀, CircleDeg1Lift.translationNumber_pow, CircleDeg1Lift.translationNumber_zpow, CircleDeg1Lift.translationNumber_mul_of_commute, CircleDeg1Lift.translationNumber_units_inv, CircleDeg1Lift.translationNumber_translate, CircleDeg1Lift.translationNumber_one, CircleDeg1Lift.dist_map_zero_lt_of_semiconj, CircleDeg1Lift.translationNumber_conj_eq, CircleDeg1Lift.translationNumber_mono, CircleDeg1Lift.translationNumber_eq_of_dist_bounded, CircleDeg1Lift.translationNumber_le_of_le_add, CircleDeg1Lift.le_translationNumber_of_add_le, CircleDeg1Lift.floor_sub_le_translationNumber, CircleDeg1Lift.map_lt_add_translationNumber_add_one, CircleDeg1Lift.translationNumber_of_map_pow_eq_add_int, CircleDeg1Lift.translationNumber_eq_int_iff, CircleDeg1Lift.units_semiconj_of_translationNumber_eq, CircleDeg1Lift.semiconj_of_bijective_of_translationNumber_eq]
  E1: []
families: []
requires: [V13, V15, V21.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The translation number

### Overview

A lift $F$ of degree one moves each point by $F(x) - x$, a periodic function. The translation number is the average of this displacement along an orbit: $\tau(F) = \lim F^n(x)/n$. For the lift of a circle homeomorphism, $\tau(F)$ modulo $1$ is the rotation number of Poincaré. This section proves that the limit exists, that it is a conjugacy invariant, and that for a continuous lift it is rational exactly when there is a periodic orbit. It uses the bounds of Section 1 throughout.

### Definitions

**Definition (Translation number).** The *translation number* of a lift $F$ of degree one is
$$\tau(F) = \lim_{n \to \infty} \frac{F^n(0)}{n}.$$

Mathlib defines $\tau(F)$ as the limit of the subsequence $F^{2^n}(0)/2^n$.

::: mathlib
`CircleDeg1Lift.translationNumber` · `Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber`

`translationNumber : CircleDeg1Lift → ℝ`. The auxiliary sequence is `transnumAuxSeq f n = (f ^ 2 ^ n) 0 / 2 ^ n`, and `transnumAuxSeq_dist_lt` gives `dist (f.transnumAuxSeq n) (f.transnumAuxSeq (n + 1)) < 1 / 2 / 2 ^ n`. The definition is its limit. The lemma `translationNumber_eq_of_tendsto₀` identifies the limit of `(⇑f)^[n] 0 / ↑n` with it.

<?decl CircleDeg1Lift.translationNumber?>
:::

### Theorems and proofs

Write $a_n = F^n(0)$.

**Theorem (Existence of the translation number).** The sequence $a_n/n$ converges to a real number $\tau(F)$, and $|F^n(0) - n\tau(F)| \le 1$ for all $n$.

*Proof.* Apply the composition bound of Section 1 to the lifts $F^m$ and $F^n$: $|F^m(F^n(0)) - F^m(0) - F^n(0)| < 1$, that is $|a_{m+n} - a_m - a_n| < 1$. By induction on $k$, $|a_{kn} - k a_n| < k$ for $k \ge 1$. Divide by $kn$: $|a_{kn}/(kn) - a_n/n| < 1/n$. With the roles of $m$ and $n$ exchanged, $|a_{mn}/(mn) - a_m/m| < 1/m$. So
$$\left|\frac{a_m}{m} - \frac{a_n}{n}\right| < \frac1m + \frac1n,$$
and $(a_n/n)$ is a Cauchy sequence. Let $\tau$ be its limit. Let $k \to \infty$ in $|a_{kn}/(kn) - a_n/n| < 1/n$: then $|\tau - a_n/n| \le 1/n$, so $|a_n - n\tau| \le 1$. $\square$ The argument is that of Fekete's lemma (Volume 15, Chapter 1, Exercise 6).

**Proposition (Any starting point).** For each $x \in \mathbb{R}$, $(F^n(x) - x)/n \to \tau(F)$.

*Proof.* For any lift $G$ and any $x$, $|G(x) - x - G(0)| < 1$. By periodicity take $x \in [0, 1)$; then $G(0) \le G(x) \le G(0) + 1$ and $0 \le x < 1$ give the bound. Apply it to $G = F^n$ and divide by $n$. $\square$

**Proposition (Powers, products, translations).** For lifts $F$ and $G$ and $k \ge 0$:

1. $\tau(F^k) = k\,\tau(F)$.
2. If $F \circ G = G \circ F$, then $\tau(F \circ G) = \tau(F) + \tau(G)$.
3. $\tau(T_a) = a$ and $\tau(\mathrm{id}) = 0$. If $F$ is a unit, then $\tau(F^{-1}) = -\tau(F)$.

*Proof.* (1) $a_{kn}/n = k \cdot a_{kn}/(kn) \to k\tau(F)$. (2) Since $F$ and $G$ commute, $(F \circ G)^n = F^n \circ G^n$, and the composition bound gives $|(F\circ G)^n(0) - F^n(0) - G^n(0)| < 1$. Divide by $n$. (3) $T_a^n(0) = na$. The lifts $F$ and $F^{-1}$ commute, so (2) gives $\tau(F) + \tau(F^{-1}) = \tau(\mathrm{id}) = 0$. $\square$

**Theorem (Semiconjugacy invariance).** Let $H$, $G_1$, $G_2$ be lifts with $H \circ G_1 = G_2 \circ H$. Then $\tau(G_1) = \tau(G_2)$. In particular $\tau(H G H^{-1}) = \tau(G)$ for a unit $H$.

*Proof.* First $|G_1(0) - G_2(0)| < 2$: the composition bound gives $|H(G_1(0)) - H(0) - G_1(0)| < 1$ and $|G_2(H(0)) - G_2(0) - H(0)| < 1$, and $H(G_1(0)) = G_2(H(0))$. The relation $H \circ G_1^n = G_2^n \circ H$ holds for all $n$ by induction, so $|G_1^n(0) - G_2^n(0)| < 2$. Divide by $n$. $\square$

The same argument proves: if $|F^n(0) - G^n(0)| \le C$ for all $n$, then $\tau(F) = \tau(G)$.

**Proposition (Bounds from one inequality).** Let $F$ be a lift and $z \in \mathbb{R}$.

1. If $F \le G$ pointwise, then $\tau(F) \le \tau(G)$.
2. If $F(x) \le x + z$ for all $x$, then $\tau(F) \le z$. If $x + z \le F(x)$ for all $x$, then $z \le \tau(F)$.
3. For each $x$, $\lfloor F(x) - x \rfloor \le \tau(F)$ and $F(x) < x + \tau(F) + 1$.

*Proof.* (1) By induction $F^n(0) \le G^n(0)$: $F^{n+1}(0) = F(F^n(0)) \le F(G^n(0)) \le G(G^n(0))$. (2) By induction $F^n(0) \le nz$, since $F^{n+1}(0) \le F^n(0) + z$. (3) Put $m = \lfloor F(x) - x \rfloor \in \mathbb{Z}$, so $x + m \le F(x)$. The iterate bound of Section 1 gives $x + nm \le F^n(x)$, so $m \le \tau(F)$ by the proposition on starting points. Then $F(x) - x < m + 1 \le \tau(F) + 1$. $\square$

**Theorem (Continuous lifts realise the translation number).** If $F$ is continuous, then there is $x$ with $F(x) = x + \tau(F)$.

*Proof.* The function $g(x) = F(x) - x$ is continuous with period $1$, so it attains a minimum $a$ and a maximum $b$ on $[0, 1]$, and these are its minimum and maximum on $\mathbb{R}$. Then $x + a \le F(x) \le x + b$ for all $x$, and part (2) above gives $a \le \tau(F) \le b$. By the intermediate value theorem, $g$ takes the value $\tau(F)$. $\square$

**Theorem (Rational translation number).** Let $n > 0$ and $m \in \mathbb{Z}$.

1. If $F^n(x) = x + m$ for some $x$, then $\tau(F) = m/n$. No continuity is needed.
2. If $F$ is continuous and $\tau(F) = m/n$, then $F^n(x) = x + m$ for some $x$.

*Proof.* (1) $F^n$ commutes with $T_m$, so $F^{kn}(x) = x + km$ by induction. Then $(F^{kn}(x) - x)/(kn) = m/n$ for all $k$, and this subsequence converges to $\tau(F)$. (2) The lift $F^n$ is continuous and $\tau(F^n) = n\tau(F) = m$. The previous theorem gives $x$ with $F^n(x) = x + m$. $\square$

On the circle, $F^n(x) = x + m$ says that $\pi(x)$ has period dividing $n$. So a circle homeomorphism has a periodic orbit if and only if its rotation number is rational.

**Theorem (Poincaré, Ghys).** Let $\Gamma$ be a group and $\rho_1, \rho_2 : \Gamma \to$ (lifts) be monoid homomorphisms with $\tau(\rho_1(g)) = \tau(\rho_2(g))$ for all $g \in \Gamma$. Then there is a lift $H$ with $H \circ \rho_1(g) = \rho_2(g) \circ H$ for all $g$.

*Proof.* Each $\rho_i(g)$ is a unit, with inverse $\rho_i(g^{-1})$, so it is an order isomorphism of $\mathbb{R}$. Put
$$H(x) = \sup_{g \in \Gamma} \rho_2(g^{-1})\big(\rho_1(g)(x)\big).$$
The supremum is finite. By part (3) of the proposition on bounds, applied twice, and by $\tau(\rho_2(g^{-1})) = -\tau(\rho_2(g)) = -\tau(\rho_1(g))$,
$$\rho_2(g^{-1})(\rho_1(g)(x)) < \rho_1(g)(x) - \tau(\rho_1(g)) + 1 < x + 2.$$
So $x \le H(x) \le x + 2$, where the lower bound is the term $g = 1$. Each term is a lift, so $H$ is monotone and $H(x + 1) = H(x) + 1$. For $h \in \Gamma$, put $g' = gh$:
$$H(\rho_1(h)(x)) = \sup_{g'} \rho_2(h)\,\rho_2(g'^{-1})\,\rho_1(g')(x) = \rho_2(h)(H(x)),$$
because the order isomorphism $\rho_2(h)$ preserves suprema. $\square$

### Examples

**Example (A rational number by computation).** Let $F(x) = x + \tfrac12 + \tfrac{b}{2\pi}\sin(4\pi x)$ with $|b| \le \tfrac12$. Then $F'(x) = 1 + 2b\cos(4\pi x) \ge 0$, so $F$ is a continuous lift. Now $F(0) = \tfrac12$ and $F(\tfrac12) = 1 + \tfrac{b}{2\pi}\sin(2\pi) = 1$. So $F^2(0) = 0 + 1$, and $\tau(F) = \tfrac12$ by part (1) of the theorem on rational numbers.

**Example (Rotations).** $\tau(H \circ T_a \circ H^{-1}) = a$ for a unit $H$. So for $a \notin \mathbb{Q}$ no conjugate of $T_a$ has a periodic orbit.

**Counterexample (Continuity is needed).** Let $F(x) = \lfloor x \rfloor + \tfrac12(\operatorname{fract}(x) + 1)$. It is a strictly increasing lift, not continuous. On $[0, 1)$, $F(x) = (x+1)/2$, so $F(x) - x = (1 - x)/2 \in (0, \tfrac12]$. The orbit of $0$ is $\tfrac12, \tfrac34, \tfrac78, \dots$, always in $[0, 1)$, so $\tau(F) = 0$. But $F^n(x) - x \in (0, 1)$ for all $x$ and $n \ge 1$, so $F^n(x) = x + m$ has no solution. Part (2) of the theorem fails without continuity.

### The library around it

::: mathlib
`CircleDeg1Lift.tendsto_translationNumber` · `Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber`

`Tendsto (fun n ↦ ((f ^ n) x - x) / ↑n) atTop (𝓝 f.translationNumber)`. The quantitative form at $0$ is `dist_pow_map_zero_mul_translationNumber_le : dist ((f ^ n) 0) (↑n * f.translationNumber) ≤ 1`. The algebraic rules are `translationNumber_pow`, `translationNumber_zpow`, `translationNumber_mul_of_commute` and `translationNumber_units_inv`.

<?decl CircleDeg1Lift.tendsto_translationNumber?>
:::

::: mathlib
`CircleDeg1Lift.translationNumber_eq_of_semiconj` · `Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber`

`Function.Semiconj ⇑f ⇑g₁ ⇑g₂ → g₁.translationNumber = g₂.translationNumber`. The key step is `dist_map_zero_lt_of_semiconj`, with bound `2`. The conjugation form is `translationNumber_conj_eq`, and `translationNumber_eq_of_dist_bounded` is the bounded distance criterion. Order bounds are `translationNumber_mono`, `translationNumber_le_of_le_add`, `le_translationNumber_of_add_le`, `floor_sub_le_translationNumber` and `map_lt_add_translationNumber_add_one`.

<?decl CircleDeg1Lift.translationNumber_eq_of_semiconj?>
:::

::: mathlib
`CircleDeg1Lift.translationNumber_eq_rat_iff` · `Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber`

`Continuous ⇑f → 0 < n → (f.translationNumber = ↑m / ↑n ↔ ∃ x, (f ^ n) x = x + ↑m)`. The direction without continuity is `translationNumber_of_map_pow_eq_add_int`. The case $n = 1$ is `translationNumber_eq_int_iff`, and the realisation theorem is `exists_eq_add_translationNumber`.

<?decl CircleDeg1Lift.translationNumber_eq_rat_iff?>
:::

::: mathlib
`CircleDeg1Lift.semiconj_of_group_action_of_forall_translationNumber_eq` · `Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber`

For `f₁ f₂ : G →* CircleDeg1Lift` on a group `G` with equal translation numbers, `∃ F, ∀ g, Function.Semiconj ⇑F ⇑(f₁ g) ⇑(f₂ g)`. The docstring cites Ghys. The corollaries for one map are `units_semiconj_of_translationNumber_eq` and `semiconj_of_bijective_of_translationNumber_eq`.

<?decl CircleDeg1Lift.semiconj_of_group_action_of_forall_translationNumber_eq?>
:::

The index of this edition has no declaration for Denjoy's theorem, which says that a $C^2$ diffeomorphism of the circle with irrational rotation number $a$ is conjugate to the rotation by $a$ by a homeomorphism.

Common errors of a learner:

- The rotation number of the circle map is the class of $\tau(F)$ modulo $1$. Two lifts of one circle map differ by an integer translation.
- `translationNumber_eq_rat_iff` needs `Continuous ⇑f`, as the counterexample shows.
- `translationNumber_mul_of_commute` needs `Commute f g`. In general $\tau(F \circ G) \ne \tau(F) + \tau(G)$.

### Exercises

1. (A) Compute $\tau(F)$ for $F(x) = x + \tfrac13 + \tfrac{b}{2\pi}\sin(6\pi x)$ with $|b| \le \tfrac13$. Hint: compute $F(0)$, $F(\tfrac13)$ and $F(\tfrac23)$.
2. (B) Show that $F \mapsto \tau(F)$ is continuous for the uniform distance $\sup_x |F(x) - G(x)|$. Hint: if $F \le G \le T_\varepsilon \circ F$, then $\tau(F) \le \tau(G) \le \tau(F) + \varepsilon$.
3. (B) Let $F$ be continuous with $\tau(F) \notin \mathbb{Q}$. Show that $F^n(x) - x \notin \mathbb{Z}$ for all $x$ and $n \ge 1$, and that for each $n$ some $x$ has $F^n(x) = x + n\tau(F)$.
4. (B) Let $F_a(x) = x + a + \tfrac{1}{4\pi}\sin(2\pi x)$. Show that $a \mapsto \tau(F_a)$ is continuous, monotone, and takes every real value.
5. (C) For $F_a$ as in Exercise 4, show that $\{a : \tau(F_a) = 0\}$ is an interval of positive length. Hint: $F_a$ has a fixed point if and only if $|a| \le \tfrac{1}{4\pi}$.

### Notes and history

Poincaré introduced the rotation number in the 1880s, in his memoirs on curves defined by differential equations, and proved that it is rational exactly when there is a periodic orbit. Denjoy proved his theorem in 1932. The semiconjugacy theorem for group actions is in the work of Ghys, which the Mathlib docstring cites.

### Reference

<?reference?>
