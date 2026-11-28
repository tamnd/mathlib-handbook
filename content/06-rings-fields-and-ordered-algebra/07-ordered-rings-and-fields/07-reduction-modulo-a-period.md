---
title: Reduction to an interval modulo a period
kind: api
modules:
  - Mathlib.Algebra.Order.ToIntervalMod
explains:
  E2: [toIcoDiv, toIcoMod, toIocMod, toIcoDiv_eq_iff, toIcoMod_add_toIcoDiv_zsmul, toIcoMod_eq_toIcoMod, toIcoMod_eq_fract_mul, AddCommGroup.tfae_modEq, QuotientAddGroup.equivIcoMod, QuotientAddGroup.circularOrder]
  E1: auto
families: []
requires: [V06.C03, V04, V05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Reduction to an interval modulo a period

### Overview

An angle is a real number up to multiples of $2\pi$. To compute with angles one often picks a representative in a fixed interval, such as $[0, 2\pi)$ or $(-\pi, \pi]$. The module `Mathlib.Algebra.Order.ToIntervalMod` gives this reduction for any period $p > 0$ in an archimedean ordered additive group $\alpha$. For a base point $a$, each $b \in \alpha$ has exactly one representative $b - n p$ in the half-open interval $[a, a + p)$, and exactly one in $(a, a + p]$. The functions `toIcoMod` and `toIocMod` return these representatives, and `toIcoDiv` and `toIocDiv` return the integer $n$.

The section needs the archimedean property of Section 3, which gives the existence of $n$, the floor function of Sections 3 and 6 for the formulas in a field, and the quotient groups of Volume 5. The reduction is used for the type `Real.Angle` and for the additive circle in Volume 15.

### The library around it

#### The four functions

All four functions take the proof `hp : 0 < p` as an explicit argument, then the base point $a$ and the element $b$.

| Lean name | Value |
| --- | --- |
| `toIcoDiv hp a b` | the integer $n$ with $b - n p \in [a, a + p)$ |
| `toIocDiv hp a b` | the integer $n$ with $b - n p \in (a, a + p]$ |
| `toIcoMod hp a b` | $b - (\operatorname{toIcoDiv} \, a \, b) \, p \in [a, a + p)$ |
| `toIocMod hp a b` | $b - (\operatorname{toIocDiv} \, a \, b) \, p \in (a, a + p]$ |

The defining property is `toIcoDiv_eq_iff`: $\operatorname{toIcoDiv}(a, b) = n \iff b - n p \in [a, a + p)$. Existence and uniqueness of $n$ come from the archimedean property. Proof of uniqueness: if $b - np$ and $b - mp$ are both in $[a, a + p)$, then their difference $(m - n)p$ lies in $(-p, p)$, so $m = n$. Existence uses the existence of a unique integer $n$ with $n p \le b - a < (n + 1) p$, which is `existsUnique_zsmul_near_of_pos` in the module `Mathlib.Algebra.Order.Archimedean.Basic` of Section 3.

The main identities are `toIcoMod_mem_Ico`, which places the value in $[a, a + p)$, and `toIcoMod_add_toIcoDiv_zsmul`: $\operatorname{toIcoMod}(a, b) + \operatorname{toIcoDiv}(a, b) \cdot p = b$. The lemma `self_sub_toIcoMod` gives the same identity in the form $b - \operatorname{toIcoMod}(a, b) = \operatorname{toIcoDiv}(a, b) \cdot p$. The interval form is `toIcoMod_eq_self`: the function fixes $b$ exactly when $b$ is already in $[a, a + p)$.

#### The formulas in a field

In a linearly ordered field with a floor, the functions have closed forms. The lemma `toIcoDiv_eq_floor` says $\operatorname{toIcoDiv}(a, b) = \lfloor (b - a)/p \rfloor$, and `toIocDiv_eq_neg_floor` gives the other one as $-\lfloor (a + p - b)/p \rfloor$. For the base point $0$, `toIcoMod_eq_fract_mul` says
$$\operatorname{toIcoMod}(0, b) = \{b / p\} \cdot p,$$
where $\{\cdot\}$ is the fractional part. With $p = 1$ this is `toIcoMod_zero_one`: the reduction to $[0, 1)$ is the fractional part. So `toIcoMod` is the generalization of `Int.fract` to any period and any archimedean group.

#### Periodicity and translation

Each function is periodic in $b$: `toIcoMod_periodic` says that `toIcoMod hp a` is periodic with period $p$, and `toIcoMod_add_zsmul` says $\operatorname{toIcoMod}(a, b + m p) = \operatorname{toIcoMod}(a, b)$ for $m \in \mathbb{Z}$. The integer part moves with $b$: `toIcoDiv_add_zsmul` says $\operatorname{toIcoDiv}(a, b + m p) = \operatorname{toIcoDiv}(a, b) + m$. The library has forms for multiples written with natural scalars, with casts of natural numbers and integers, and with numerals, and with the multiple on either side, so that a rewrite finds its pattern. The case $m = 1$ is `toIcoDiv_add_right`, $\operatorname{toIcoDiv}(a, b + p) = \operatorname{toIcoDiv}(a, b) + 1$, and `toIcoMod_add_right`, $\operatorname{toIcoMod}(a, b + p) = \operatorname{toIcoMod}(a, b)$.

A change of the base point does not change the class of the result. `toIcoMod_toIcoMod` says that reducing first with base $a_2$ and then with base $a_1$ is the same as reducing with base $a_1$. Negation exchanges the two kinds of interval: `toIcoMod_neg` says $\operatorname{toIcoMod}(a, -b) = p - \operatorname{toIocMod}(-a, b)$.

#### Congruence modulo the period

The relation `AddCommGroup.ModEq p a b`, written `a ≡ b [PMOD p]`, says that $b - a$ is an integer multiple of $p$. The reduction is a complete invariant of this relation: `toIcoMod_inj` says $\operatorname{toIcoMod}(c, a) = \operatorname{toIcoMod}(c, b) \iff a \equiv b \pmod p$, and `toIcoMod_eq_toIcoMod` is the form with an explicit multiple. Proof: both values are in $[c, c + p)$, and they differ from $a$ and $b$ by multiples of $p$. So they are equal exactly when $a - b$ is a multiple of $p$, by the uniqueness of the representative.

The two kinds of interval differ exactly at the end points. `toIcoMod_le_toIocMod` says $\operatorname{toIcoMod}(a, b) \le \operatorname{toIocMod}(a, b)$, and the theorem `AddCommGroup.tfae_modEq` lists four equivalent conditions:

1. $a \equiv b \pmod p$;
2. no translate $b - z p$ lies in the open interval $(a, a + p)$;
3. $\operatorname{toIcoMod}(a, b) \neq \operatorname{toIocMod}(a, b)$;
4. $\operatorname{toIcoMod}(a, b) + p = \operatorname{toIocMod}(a, b)$.

Proof idea: if $b \equiv a$, then the representative in $[a, a + p)$ is $a$ and the one in $(a, a + p]$ is $a + p$. Otherwise both representatives are in the open interval and are equal. The lemmas `AddCommGroup.modEq_iff_toIcoMod_eq_left` and `AddCommGroup.not_modEq_iff_toIcoMod_eq_toIocMod` are single parts of this list. In the integer parts, `toIocDiv_wcovBy_toIcoDiv` says that `toIcoDiv` is `toIocDiv` or one more.

#### The quotient and the circular order

The quotient $\alpha / p\mathbb{Z}$ is `α ⧸ AddSubgroup.zmultiples p`. The equivalence `QuotientAddGroup.equivIcoMod hp a` identifies it with the interval $[a, a + p)$, and `QuotientAddGroup.equivIocMod` with $(a, a + p]$. The inverse map is the restriction of the quotient map, and the forward map is `toIcoMod` on representatives, which is well defined by `toIcoMod_inj`.

The quotient is not linearly ordered, but it has a circular order: for three points $x, y, z$ on the circle, `btw x y z` says that $y$ lies on the arc from $x$ to $z$ in the positive direction. The instance `QuotientAddGroup.circularOrder` gives this order when `Fact (0 < p)` holds. The lemma `QuotientAddGroup.btw_coe_iff` says that `btw` holds for the images of $a, b, c$ exactly when $\operatorname{toIcoMod}(a, b) \le \operatorname{toIocMod}(a, c)$, that is, when $b$ comes before $c$ after the reduction to the interval that starts at $a$. The mix of the two kinds of interval handles the case $c \equiv a$, where $c$ counts as the end point $a + p$.

#### The covering by intervals

The translates of a fundamental interval cover the group. The lemma `iUnion_Ico_add_zsmul` says $\bigcup_{n \in \mathbb{Z}} [a + np, a + (n + 1)p) = \alpha$, and the forms `iUnion_Ioc_add_zsmul` and `iUnion_Icc_add_zsmul` are for the other intervals. For $p = 1$ in a ring, `iUnion_Ico_intCast` says $\bigcup_n [n, n + 1) = \alpha$. The intervals $[a + np, a + (n+1)p)$ are pairwise disjoint; the closed intervals overlap at the end points.

#### Common errors

1. The proof `hp : 0 < p` is an explicit argument. Write `toIcoMod hp a b`, not `toIcoMod p a b`. The interval is $[a, a + p)$, so the base point is the left end point, not the centre.
2. `toIcoMod` and `toIocMod` differ only at the multiples of $p$ shifted by $a$. A lemma about one does not transfer to the other without `AddCommGroup.tfae_modEq` or `toIcoMod_le_toIocMod`.
3. For the symmetric interval $(-p/2, p/2]$, use `toIocMod hp (-(p/2)) b`. The base point is $-p/2$, and the interval has length $p$.

### Exercises

1. (A) Compute $\operatorname{toIcoMod}(0, 17/3)$ and $\operatorname{toIcoDiv}(0, 17/3)$ for the period $p = 2$ in $\mathbb{Q}$.
2. (A) Compute $\operatorname{toIcoMod}(0, 4)$ and $\operatorname{toIocMod}(0, 4)$ for $p = 2$, and check the fourth condition of `AddCommGroup.tfae_modEq`.
3. (B) Prove the uniqueness of $n$ in `toIcoDiv_eq_iff` from the archimedean property.
4. (B) Show $\operatorname{toIcoMod}(a, b) = \operatorname{toIcoMod}(0, b - a) + a$.
5. (B) Use `toIcoMod_eq_fract_mul` to prove that $\operatorname{toIcoMod}(0, b)$ for $p = 2\pi$ is $b - 2\pi\lfloor b/(2\pi) \rfloor$.
6. (C) Prove that `QuotientAddGroup.equivIcoMod` is well defined: if $a \equiv b \pmod p$, then $\operatorname{toIcoMod}(c, a) = \operatorname{toIcoMod}(c, b)$.

### Reference

<?reference?>
