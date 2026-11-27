---
title: Lifts of degree one
kind: theory
modules:
  - Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber
explains:
  E3: [CircleDeg1Lift, CircleDeg1Lift.map_add_int, CircleDeg1Lift.isUnit_iff_bijective, CircleDeg1Lift.instLattice, CircleDeg1Lift.map_map_zero_lt, CircleDeg1Lift.continuous_iff_surjective, CircleDeg1Lift.iterate_le_of_map_le_add_int]
  E2: [CircleDeg1Lift.instMonoid, CircleDeg1Lift.coe_mul, CircleDeg1Lift.coe_pow, CircleDeg1Lift.toOrderIso, CircleDeg1Lift.translate, CircleDeg1Lift.translate_apply, CircleDeg1Lift.translate_iterate, CircleDeg1Lift.commute_add_int, CircleDeg1Lift.map_int_of_map_zero, CircleDeg1Lift.map_le_of_map_zero, CircleDeg1Lift.le_map_of_map_zero, CircleDeg1Lift.lt_map_map_zero, CircleDeg1Lift.dist_map_map_zero_lt, CircleDeg1Lift.le_floor_map_map_zero, CircleDeg1Lift.mul_floor_map_zero_le_floor_iterate_zero, CircleDeg1Lift.forall_map_sub_of_Icc, CircleDeg1Lift.map_fract_sub_fract_eq, CircleDeg1Lift.sup_apply, CircleDeg1Lift.iterate_pos_le_iff, CircleDeg1Lift.le_iterate_of_add_int_le_map, CircleDeg1Lift.semiconjBy_iff_semiconj, CircleDeg1Lift.commute_iff_commute]
  E1: auto
families: []
requires: [V13, V15, V21.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Lifts of degree one

### Overview

The circle is $\mathbb{R}/\mathbb{Z}$, with the quotient map $\pi$. The circle has no order, so an orientation preserving homeomorphism $f$ of the circle is studied through a lift: an increasing homeomorphism $F$ of $\mathbb{R}$ with $\pi \circ F = f \circ \pi$ and $F(x + 1) = F(x) + 1$. Mathlib takes a wider class: a lift is only monotone. This section proves the bounds on $F(x) - x$ that the translation number of Section 2 needs, and shows that the lifts form a monoid and a lattice.

### Definitions

**Definition (Lift of degree one).** A *lift of degree one* is a monotone map $F : \mathbb{R} \to \mathbb{R}$ with $F(x + 1) = F(x) + 1$ for all $x$.

Such an $F$ induces a map $f$ of the circle by $f(\pi(x)) = \pi(F(x))$, well defined by the lemma below.

::: mathlib
`CircleDeg1Lift` · `Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber`

The structure `CircleDeg1Lift` extends the bundled monotone maps `ℝ →o ℝ` by the field `map_add_one' : ∀ x, toFun (x + 1) = toFun x + 1`. Continuity is a separate hypothesis `Continuous ⇑f`, and a lift of a homeomorphism is a unit of the monoid below.

<?decl CircleDeg1Lift?>
:::

**Definition (Translation).** For $a \in \mathbb{R}$ the *translation* $T_a(x) = x + a$ is a lift of degree one. It induces a rotation of the circle.

### Theorems and proofs

**Lemma (Integer shifts).** Let $F$ be a lift of degree one. Then $F(x + m) = F(x) + m$ for all $x \in \mathbb{R}$ and $m \in \mathbb{Z}$. In particular $F(m) = F(0) + m$, and the function $F(x) - x$ has period $1$.

*Proof.* For $m \ge 0$ use induction on $m$: $F(x + m + 1) = F(x + m) + 1 = F(x) + m + 1$. For $m < 0$ apply this to $y = x + m$ and $-m > 0$: $F(x) = F(y) - m$. Then $F(x + 1) - (x + 1) = F(x) - x$. $\square$

**Proposition (Bounds at one point).** Let $F$ be a lift of degree one. For all $x$,
$$F(0) + \lfloor x \rfloor \le F(x) \le F(0) + \lceil x \rceil.$$

*Proof.* From $\lfloor x \rfloor \le x \le \lceil x \rceil$ and monotonicity, $F(\lfloor x \rfloor) \le F(x) \le F(\lceil x \rceil)$. The lemma gives $F(\lfloor x \rfloor) = F(0) + \lfloor x \rfloor$ and $F(\lceil x \rceil) = F(0) + \lceil x \rceil$. $\square$

**Theorem (Composition is almost additive at zero).** Let $F$ and $G$ be lifts of degree one. Then
$$F(0) + G(0) - 1 < F(G(0)) < F(0) + G(0) + 1.$$

*Proof.* Apply the proposition to $F$ at the point $x = G(0)$: $F(0) + \lfloor G(0) \rfloor \le F(G(0)) \le F(0) + \lceil G(0) \rceil$. Then use $\lfloor y \rfloor > y - 1$ and $\lceil y \rceil < y + 1$ for $y = G(0)$. $\square$

Section 2 gets the limit of $F^n(0)/n$ from this estimate. The same proof with floors gives $\lfloor F(0) \rfloor + \lfloor G(0) \rfloor \le \lfloor F(G(0)) \rfloor$, and by induction $n \lfloor F(0) \rfloor \le \lfloor F^n(0) \rfloor$.

**Proposition (Monoid and units).** The lifts of degree one form a monoid under composition, with the identity as unit element. A lift is invertible in this monoid if and only if it is bijective, and then its inverse is an increasing bijection of $\mathbb{R}$, an order isomorphism.

*Proof.* A composition of monotone maps is monotone, and $F(G(x + 1)) = F(G(x)) + 1$. An inverse in the monoid is an inverse map, so a unit is bijective. Conversely a monotone bijection $F$ of $\mathbb{R}$ is strictly increasing, and its inverse map $G$ is increasing. For $y = F(x)$, $F(x + 1) = y + 1$ gives $G(y + 1) = x + 1 = G(y) + 1$. So $G$ is a lift, the inverse of $F$ in the monoid. $\square$

**Proposition (Lattice).** For lifts $F$ and $G$, the pointwise maximum $x \mapsto \max(F(x), G(x))$ and the pointwise minimum are lifts of degree one. With the pointwise order, the lifts form a lattice.

*Proof.* The maximum of two monotone functions is monotone, and $\max(F(x) + 1, G(x) + 1) = \max(F(x), G(x)) + 1$. The minimum is the same. $\square$

This is the reason for the wide definition. A supremum of infinitely many continuous lifts need not be continuous (Exercise 5), and Section 2 builds a semiconjugacy as such a supremum.

**Theorem (Continuity and surjectivity).** A lift of degree one is continuous if and only if it is surjective.

*Proof.* By the bounds at one point, $F(x) \to \pm\infty$ as $x \to \pm\infty$. If $F$ is continuous, then $F(\mathbb{R})$ is an interval by the intermediate value theorem (Volume 15, Chapter 2), unbounded in both directions, so it is $\mathbb{R}$. Conversely let $F$ be surjective, and let $x_0 \in \mathbb{R}$. A monotone function has one-sided limits $F(x_0^-) \le F(x_0) \le F(x_0^+)$. If $F(x_0^-) < F(x_0^+)$, then each value $v$ in the open interval $(F(x_0^-), F(x_0^+))$ with $v \ne F(x_0)$ is not taken: for $x < x_0$, $F(x) \le F(x_0^-)$, and for $x > x_0$, $F(x) \ge F(x_0^+)$. This contradicts surjectivity, so $F$ is continuous at $x_0$. $\square$

**Theorem (Iterates and integer bounds).** Let $F$ be a lift of degree one, $x \in \mathbb{R}$ and $m \in \mathbb{Z}$. If $F(x) \le x + m$, then $F^n(x) \le x + nm$ for all $n \ge 0$. If $x + m \le F(x)$, then $x + nm \le F^n(x)$. For $n > 0$ the converses hold: $F^n(x) \le x + nm$ if and only if $F(x) \le x + m$.

*Proof.* Induction on $n$. If $F^n(x) \le x + nm$, then by monotonicity and the lemma $F^{n+1}(x) = F(F^n(x)) \le F(x + nm) = F(x) + nm \le x + (n + 1)m$. The second statement has the same proof. For the converse with $n > 0$, assume $F(x) > x + m$. Then $F^n(x) > x + nm$ by induction: from $F^k(x) > x + km$ follows $F^{k+1}(x) \ge F(x + km) = F(x) + km > x + (k+1)m$. $\square$

### Examples

**Example (Rotations).** The translation $T_a$ is a lift. Its iterates are $T_a^n = T_{na}$, so $T_a^n(0)/n = a$ for every $n$. If $a = p/q$ with $q > 0$, then $T_a^q(x) = x + p$.

**Example (The Arnold family).** For $a, b \in \mathbb{R}$ put
$$F_{a,b}(x) = x + a + \frac{b}{2\pi} \sin(2\pi x).$$
Then $F_{a,b}(x + 1) = F_{a,b}(x) + 1$. The derivative is $1 + b \cos(2\pi x)$, which is $\ge 0$ everywhere if and only if $|b| \le 1$. So $F_{a,b}$ is a lift of degree one exactly when $|b| \le 1$. For $|b| < 1$ it lifts a diffeomorphism of the circle. For $|b| = 1$ it lifts a homeomorphism, since $F'$ vanishes only at isolated points.

**Example (A lift that is not continuous).** The floor function $F(x) = \lfloor x \rfloor$ is monotone and $\lfloor x + 1 \rfloor = \lfloor x \rfloor + 1$. So it is a lift of degree one. It is not continuous, and its image is $\mathbb{Z}$. The lift $F(x) = \lfloor x \rfloor + \tfrac{1}{2}(\operatorname{fract}(x) + 1)$ is strictly increasing, with a jump of size $\tfrac12$ at each integer. It induces an injective map of the circle that is not continuous.

### The library around it

::: mathlib
`CircleDeg1Lift.map_add_int` · `Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber`

`f (x + ↑m) = f x + ↑m` for `m : ℤ`. Variants are `map_int_add`, `map_add_nat` and `map_int_of_map_zero : f ↑n = f 0 + ↑n`. The commutation with integer translations is `commute_add_int`, a `Function.Commute`. The lemma `forall_map_sub_of_Icc` transfers a property of `f x - x` from `Set.Icc 0 1` to all `x`, and `map_fract_sub_fract_eq` is the periodicity.

<?decl CircleDeg1Lift.map_add_int?>
:::

::: mathlib
`CircleDeg1Lift.map_map_zero_lt` · `Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber`

`f (g 0) < f 0 + g 0 + 1`. With `lt_map_map_zero` it gives `dist_map_map_zero_lt : dist (f 0 + g 0) (f (g 0)) < 1`. The bounds at one point are `le_map_of_map_zero : f 0 + ↑⌊x⌋ ≤ f x` and `map_le_of_map_zero`. The floor forms are `le_floor_map_map_zero` and `mul_floor_map_zero_le_floor_iterate_zero : ↑n * ⌊f 0⌋ ≤ ⌊f^[n] 0⌋`.

<?decl CircleDeg1Lift.map_map_zero_lt?>
:::

::: mathlib
`CircleDeg1Lift.isUnit_iff_bijective` · `Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber`

The monoid instance `instMonoid` has `f * g` equal to the composition: `coe_mul : ⇑(f * g) = ⇑f ∘ ⇑g`, and `coe_pow : ⇑(f ^ n) = (⇑f)^[n]`. The main lemma is `IsUnit f ↔ Function.Bijective ⇑f`. The homomorphism `toOrderIso : CircleDeg1Liftˣ →* ℝ ≃o ℝ` turns a unit into an order isomorphism of the line.

<?decl CircleDeg1Lift.isUnit_iff_bijective?>
:::

::: mathlib
`CircleDeg1Lift.translate` · `Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber`

`translate : Multiplicative ℝ →* CircleDeg1Liftˣ`. The translation by `x` is `translate (Multiplicative.ofAdd x)`, and `translate_apply` says that it sends `y` to `x + y`. Since it is a homomorphism, `translate_pow` and `translate_iterate` are free.

<?decl CircleDeg1Lift.translate?>
:::

::: mathlib
`CircleDeg1Lift.continuous_iff_surjective` · `Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber`

`Continuous ⇑f ↔ Function.Surjective ⇑f`. The lattice instance `instLattice` has `sup_apply : (f ⊔ g) x = max (f x) (g x)` and `inf_apply`. The iterate bounds are `iterate_le_of_map_le_add_int`, `le_iterate_of_add_int_le_map` and `iterate_pos_le_iff`, which needs `0 < n`.

<?decl CircleDeg1Lift.continuous_iff_surjective?>
:::

The lemmas `semiconjBy_iff_semiconj` and `commute_iff_commute` identify `SemiconjBy f g₁ g₂` in the monoid with `Function.Semiconj ⇑f ⇑g₁ ⇑g₂` for the functions.

Common errors of a learner:

- A `CircleDeg1Lift` need not be continuous. The periodic orbit theorem of Section 2 has the hypothesis `Continuous ⇑f`.
- The product `f * g` applies `g` first. So `(f * g) x = f (g x)`, as `mul_apply` says.
- The translation by `x` takes the argument `Multiplicative.ofAdd x`, not `x`.

### Exercises

1. (A) Let $F$ be a lift and $m \in \mathbb{Z}$. Show that $T_m \circ F = F \circ T_m$, and that $F \circ T_a = T_a \circ F$ for all $a$ only if $F$ is a translation. Hint: evaluate at $0$.
2. (A) Show that $|F(x) - x - (F(y) - y)| < 1$ for all $x, y$ when $F$ is a lift. Hint: reduce to $x, y \in [0, 1)$ with $x \le y$ and use monotonicity.
3. (B) Let $F$ and $G$ be lifts. Show that $|F^n(0) + G^n(0) - (F \circ G)^n(0)|$ need not stay bounded when $F$ and $G$ do not commute. Hint: try the composition of two lifts of homeomorphisms with a fixed point each.
4. (B) Show that a lift that is a unit of the monoid is strictly increasing and continuous.
5. (C) Let $(F_i)_{i \in I}$ be lifts with $\sup_i F_i(0) < \infty$. Show that $F(x) = \sup_i F_i(x)$ is a lift of degree one. Give an example with continuous $F_i$ and $F$ not continuous.

### Notes and history

Poincaré introduced the lift of a circle homeomorphism and its rotation number in his work on curves defined by differential equations, in the 1880s. The Mathlib file cites Ghys for the semiconjugacy theorem of Section 2, which needs lifts that are not continuous.

### Reference

<?reference?>
