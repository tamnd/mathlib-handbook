---
title: Angles modulo 2 pi
kind: api
modules:
  - Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
explains:
  E2: [Real.Angle.two_zsmul_eq_iff, Real.Angle.cos_eq_iff_coe_eq_or_eq_neg, Real.Angle.toReal_coe_eq_self_iff, Real.Angle.sign_eq_zero_iff, Real.Angle.coe_abs_toReal_of_sign_nonneg, Real.Angle.sign_eq_of_continuousOn]
  E1: auto
families: []
requires: [V05, V13, V15.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Angles modulo 2 pi

### Overview

The sine and the cosine of Section 1 are periodic with period $2\pi$. So the real numbers $\theta$ and $\theta + 2\pi k$ give the same point $(\cos\theta, \sin\theta)$ of the unit circle. An angle in geometry is this point, not the real number. The module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` makes this precise. It defines the type `Real.Angle` as the quotient group $\mathbb{R}/2\pi\mathbb{Z}$, and it defines the sine, the cosine, the tangent and the sign of an angle.

The quotient has two advantages. First, the identities $\sin(\theta + 2\pi) = \sin\theta$ become equalities of angles, and the simp set uses them with no side conditions. Second, an angle has an addition but no order and no division, so a proof cannot use the wrong representative by accident. The cost is that halving and comparing are not available directly. The library supplies a canonical representative, `Real.Angle.toReal`, in the interval $(-\pi, \pi]$, and a sign, `Real.Angle.sign`, for these tasks.

The oriented angles of the Euclidean geometry of Volume 22 take values in `Real.Angle`. This section prepares the arithmetic of these values. It uses the sine, the cosine and $\pi$ of Section 1 and the quotient groups of Volume 5.

### The library around it

#### The type and the coercion

The definition is `Real.Angle := AddCircle (2 * π)`, the additive circle of period $2\pi$. It derives a normed additive commutative group structure, so an angle has a norm and a topology, and it has the instance of a circular order. The coercion from $\mathbb{R}$ is `Real.Angle.coe`; Lean writes it `(x : Real.Angle)`. The same map as an additive group homomorphism is `Real.Angle.coeHom`, and `Real.Angle.coe_coeHom` says that the two are equal. The map is continuous (`Real.Angle.continuous_coe`).

The coercion commutes with the group operations. The simp lemmas `Real.Angle.coe_zero`, `Real.Angle.coe_add`, `Real.Angle.coe_neg` and `Real.Angle.coe_sub` push the coercion inside. The lemmas `Real.Angle.coe_nsmul` and `Real.Angle.coe_zsmul` do the same for multiples, and `Real.Angle.natCast_mul_eq_nsmul` and `Real.Angle.intCast_mul_eq_zsmul` turn a product $n x$ in $\mathbb{R}$ into the multiple $n \bullet x$ of angles. The simp normal form is a sum of coercions, with multiples written as `n • θ`. There is no multiplication of angles.

Two real numbers give the same angle if and only if they differ by a multiple of $2\pi$:

| Lean name | Statement |
|---|---|
| `Real.Angle.coe_eq_zero_iff` | $(x : \text{Angle}) = 0 \iff \exists n \in \mathbb{Z},\ n \cdot 2\pi = x$ |
| `Real.Angle.angle_eq_iff_two_pi_dvd_sub` | $(\theta : \text{Angle}) = \psi \iff \exists k \in \mathbb{Z},\ \theta - \psi = 2\pi k$ |
| `Real.Angle.coe_two_pi` | $(2\pi : \text{Angle}) = 0$ |
| `Real.Angle.neg_coe_pi` | $-(\pi : \text{Angle}) = \pi$ |
| `Real.Angle.coe_pi_add_coe_pi` | $\pi + \pi = 0$ in Angle |
| `Real.Angle.sub_coe_pi_eq_add_coe_pi` | $\theta - \pi = \theta + \pi$ |

To prove a statement for all angles, the usual method is to reduce it to real numbers. The induction principle `Real.Angle.induction_on` does this: the tactic `induction θ using Real.Angle.induction_on` replaces an angle $\theta$ by the coercion of a real number $x$.

#### Halving and doubling

An angle has no half, because the equation $2\psi = \theta$ has two solutions. The lemma `Real.Angle.two_nsmul_coe_div_two` says that $2 \bullet (\theta/2 : \text{Angle}) = \theta$, so one half is always the coercion of $\theta/2$. The other half differs by $\pi$.

**Theorem.** For angles $\psi$ and $\theta$, $2 \bullet \psi = 2 \bullet \theta$ if and only if $\psi = \theta$ or $\psi = \theta + \pi$.

*Proof.* Write $\psi = \theta + \delta$. The equation says $2 \bullet \delta = 0$. Write $\delta$ as the coercion of a real number $d$. Then $2d = 2\pi k$ for an integer $k$, so $d = \pi k$. If $k$ is even, $\delta = 0$. If $k$ is odd, $\delta = \pi$, because $2\pi$ is zero in the quotient. Conversely, $2 \bullet \pi = 0$. $\square$

This is `Real.Angle.two_zsmul_eq_iff`, with the natural number version `Real.Angle.two_nsmul_eq_iff`. The library proves it from `Real.Angle.zsmul_eq_iff`, the general statement for $z \bullet \psi = z \bullet \theta$ with $z \ne 0$: then $\psi = \theta + k \bullet (2\pi/z)$ for some $k$ with $0 \le k < |z|$. The special cases appear often: `Real.Angle.two_nsmul_eq_zero_iff` says $2 \bullet \theta = 0 \iff \theta = 0 \lor \theta = \pi$, `Real.Angle.neg_eq_self_iff` says the same for $-\theta = \theta$, and `Real.Angle.two_nsmul_eq_pi_iff` gives the two halves $\pm\pi/2$ of $\pi$.

#### The trigonometric functions of an angle

The functions `Real.Angle.sin`, `Real.Angle.cos` and `Real.Angle.tan` are defined by the universal property of the quotient, because $\sin$ and $\cos$ are $2\pi$ periodic. The simp lemmas `Real.Angle.sin_coe`, `Real.Angle.cos_coe` and `Real.Angle.tan_coe` compute them on a coercion: `Real.Angle.sin (x : Angle) = Real.sin x`. Both `Real.Angle.continuous_sin` and `Real.Angle.continuous_cos` hold. The tangent is `Real.Angle.tan_eq_sin_div_cos`, and it has the junk value $0$ where the cosine is $0$, as `Real.tan` has.

The identities of Section 1 transfer with the same names in the namespace `Real.Angle`: `Real.Angle.sin_add`, `Real.Angle.cos_add`, `Real.Angle.cos_sq_add_sin_sq`, `Real.Angle.sin_neg`, `Real.Angle.cos_neg`, `Real.Angle.sin_add_pi`, `Real.Angle.cos_add_pi`, `Real.Angle.sin_add_pi_div_two` and `Real.Angle.cos_add_pi_div_two`. The periodic behaviour is stated with the predicates of Mathlib: `Real.Angle.sin_antiperiodic` says that $\sin(\theta + \pi) = -\sin\theta$, and `Real.Angle.tan_periodic` says that $\tan$ has period $\pi$.

The main new results describe when two angles have the same sine or the same cosine. For real numbers the answers need an integer $k$. For angles they need none.

**Theorem.** For real numbers $\theta$ and $\psi$, $\cos\theta = \cos\psi$ if and only if $\theta = \psi$ or $\theta = -\psi$ as angles.

*Proof.* By the formula for a difference of cosines, $\cos\theta - \cos\psi = -2\sin\frac{\theta + \psi}{2}\sin\frac{\theta - \psi}{2}$. This is zero if and only if one of the two sines is zero. The sine is zero exactly at the multiples of $\pi$. So $\frac{\theta - \psi}{2} = \pi k$, that is $\theta - \psi = 2\pi k$, or $\frac{\theta + \psi}{2} = \pi k$, that is $\theta + \psi = 2\pi k$. These are the two equalities of angles. $\square$

This is `Real.Angle.cos_eq_iff_coe_eq_or_eq_neg`. The companion for the sine is `Real.Angle.sin_eq_iff_coe_eq_or_add_eq_pi`: $\sin\theta = \sin\psi$ if and only if $\theta = \psi$ or $\theta + \psi = \pi$ as angles. Both have versions with angles on both sides, `Real.Angle.cos_eq_iff_eq_or_eq_neg` and `Real.Angle.sin_eq_iff_eq_or_add_eq_pi`. Together they give `Real.Angle.cos_sin_inj`: two real numbers with the same cosine and the same sine are equal as angles. The zeros follow: `Real.Angle.sin_eq_zero_iff` says $\sin\theta = 0 \iff \theta = 0 \lor \theta = \pi$, and `Real.Angle.cos_eq_zero_iff` gives the two angles $\pm\pi/2$.

Since $2\psi = 2\theta$ means $\psi = \theta$ or $\psi = \theta + \pi$, the doubled angle decides the absolute value of the sine and the cosine and the value of the tangent: `Real.Angle.abs_sin_eq_of_two_nsmul_eq`, `Real.Angle.abs_cos_eq_of_two_nsmul_eq` and `Real.Angle.tan_eq_of_two_nsmul_eq`. Each lemma has a twin with zsmul in place of nsmul, because both forms of the multiple occur in practice.

#### The representative in $(-\pi, \pi]$

The function `Real.Angle.toReal` sends an angle to its representative in the half open interval $(-\pi, \pi]$. On a coercion it is the reduction modulo $2\pi$ to the interval $(-\pi, \pi]$: `Real.Angle.toReal_coe` says that `(θ : Angle).toReal = toIocMod two_pi_pos (-π) θ`. The basic facts are these.

| Lean name | Statement |
|---|---|
| `Real.Angle.coe_toReal` | $(\theta.\mathrm{toReal} : \text{Angle}) = \theta$ |
| `Real.Angle.toReal_injective` | $\mathrm{toReal}$ is injective |
| `Real.Angle.toReal_mem_Ioc` | $\theta.\mathrm{toReal} \in (-\pi, \pi]$ |
| `Real.Angle.abs_toReal_le_pi` | $\lvert\theta.\mathrm{toReal}\rvert \le \pi$ |
| `Real.Angle.toReal_coe_eq_self_iff` | $(x : \text{Angle}).\mathrm{toReal} = x \iff -\pi < x \le \pi$ |
| `Real.Angle.toReal_pi` | $(\pi : \text{Angle}).\mathrm{toReal} = \pi$ |
| `Real.Angle.toReal_eq_zero_iff` | $\theta.\mathrm{toReal} = 0 \iff \theta = 0$ |
| `Real.Angle.sin_toReal` | $\sin(\theta.\mathrm{toReal}) = \sin\theta$ |

The proof of `Real.Angle.toReal_coe_eq_self_iff` is short. If $-\pi < x \le \pi$, then $x$ is a representative of its own class in the interval, and the representative is unique. Conversely, the value of `Real.Angle.toReal` always lies in the interval.

The map `Real.Angle.toReal` is not additive, and it is not odd: `Real.Angle.toReal_neg_eq_neg_toReal_iff` says that $(-\theta).\mathrm{toReal} = -\theta.\mathrm{toReal}$ if and only if $\theta \ne \pi$, because $-\pi$ is outside the interval. In the same way `Real.Angle.two_nsmul_toReal_eq_two_mul` says that $(2\theta).\mathrm{toReal} = 2\,\theta.\mathrm{toReal}$ exactly when $\theta.\mathrm{toReal} \in (-\pi/2, \pi/2]$, and `Real.Angle.nsmul_toReal_eq_mul` gives the general multiple. The lemmas `Real.Angle.cos_nonneg_iff_abs_toReal_le_pi_div_two` and `Real.Angle.cos_pos_iff_abs_toReal_lt_pi_div_two` read the sign of the cosine from the representative.

#### The sign of an angle

The function `Real.Angle.sign` takes values in `SignType`, the three values $-1, 0, 1$. It is defined as the sign of the sine. So the sign is $1$ for an angle strictly between $0$ and $\pi$, $-1$ for an angle strictly between $-\pi$ and $0$, and $0$ for the two angles $0$ and $\pi$. This last fact is `Real.Angle.sign_eq_zero_iff`, a direct consequence of `Real.Angle.sin_eq_zero_iff`. In geometry the sign of an oriented angle tells whether a triangle is positively or negatively oriented.

The sign is odd (`Real.Angle.sign_neg`) and changes under the addition of $\pi$ (`Real.Angle.sign_add_pi`, `Real.Angle.sign_antiperiodic`). It matches the sign of the representative: `Real.Angle.sign_toReal` says that the sign of the real number $\theta.\mathrm{toReal}$ is $\theta.\mathrm{sign}$ when $\theta \ne \pi$, and `Real.Angle.toReal_neg_iff_sign_neg` says that $\theta.\mathrm{toReal} < 0$ if and only if the sign is $-1$.

**Theorem.** If the sign of $\theta$ is $0$ or $1$, then $\theta$ is the coercion of $\lvert\theta.\mathrm{toReal}\rvert$.

*Proof.* Let $a = \theta.\mathrm{toReal}$. By `Real.Angle.toReal_nonneg_iff_sign_nonneg`, the hypothesis gives $a \ge 0$. So $\lvert a\rvert = a$, and the coercion of $a$ is $\theta$ by `Real.Angle.coe_toReal`. $\square$

This is `Real.Angle.coe_abs_toReal_of_sign_nonneg`. The mirror statement `Real.Angle.neg_coe_abs_toReal_of_sign_nonpos` gives $\theta = -\lvert\theta.\mathrm{toReal}\rvert$ when the sign is $0$ or $-1$. Together they show that an angle is determined by its sign and by $\lvert\theta.\mathrm{toReal}\rvert$, a number in $[0, \pi]$. The sign of a doubled angle is `Real.Angle.sign_two_nsmul_eq_sign_iff`: it equals the sign of $\theta$ if and only if $\theta = \pi$ or $\lvert\theta.\mathrm{toReal}\rvert < \pi/2$. The lemma `Real.Angle.toReal_add_eq_toReal_add_toReal` gives conditions on the signs under which `Real.Angle.toReal` is additive.

The sign is continuous away from $0$ and $\pi$ (`Real.Angle.continuousAt_sign`), because the sine is continuous and nonzero there. A consequence is a form of the intermediate value theorem of Chapter 2.

**Theorem.** Let $f$ be a continuous function from a connected set $s$ to the angles, with $f(z) \ne 0$ and $f(z) \ne \pi$ for all $z \in s$. Then all values $f(z)$ have the same sign.

*Proof.* By `ContinuousOn.angle_sign_comp`, the composite $\mathrm{sign} \circ f$ is continuous on $s$. Its image is connected. A connected subset of the discrete type `SignType` has at most one point. $\square$

This is `Real.Angle.sign_eq_of_continuousOn`. Geometry uses it to show that an oriented angle keeps its sign while a point moves without crossing a line.

#### Common errors

1. Writing `θ / 2` for an angle. There is no division on `Real.Angle`. Write the angle as the coercion of a real number and halve the real number, or use `Real.Angle.two_nsmul_eq_iff` and treat the two halves.
2. Assuming that `Real.Angle.toReal` is additive or odd. It fails at the boundary: $(\pi : \text{Angle}).\mathrm{toReal} = \pi$, but $(-\pi : \text{Angle}).\mathrm{toReal}$ is also $\pi$. Check the hypotheses of `Real.Angle.toReal_neg_eq_neg_toReal_iff` and `Real.Angle.toReal_add_eq_toReal_add_toReal`.
3. Confusing `Real.Angle.sin` with `Real.sin`. After the coercion, `simp` rewrites with `Real.Angle.sin_coe`. A goal with `Real.Angle.sin θ` for an abstract angle needs `Real.Angle.induction_on` or `Real.Angle.sin_toReal` first.

### Exercises

1. (A) Show that $(7\pi/2 : \text{Angle}) = (-\pi/2 : \text{Angle})$ and compute its `Real.Angle.toReal`, its sine and its sign.
2. (A) Show that $3 \bullet (2\pi/3 : \text{Angle}) = 0$, and find all angles $\theta$ with $3 \bullet \theta = 0$. Hint: `Real.Angle.nsmul_eq_iff`.
3. (A) Show that $-\theta = \theta$ implies $\sin\theta = 0$, from `Real.Angle.neg_eq_self_iff`.
4. (B) Prove that $\sin\theta = \sin\psi$ and $\cos\theta = \cos\psi$ imply $\theta = \psi$ for angles, from the two characterizations by the sine and by the cosine.
5. (B) Show that $(\theta + \psi).\mathrm{toReal} = \theta.\mathrm{toReal} + \psi.\mathrm{toReal}$ if and only if $\theta.\mathrm{toReal} + \psi.\mathrm{toReal} \in (-\pi, \pi]$.
6. (C) Let $f : [0, 1] \to \text{Angle}$ be continuous with $f(0)$ of sign $1$ and $f(1)$ of sign $-1$. Show that $f(t) = 0$ or $f(t) = \pi$ for some $t$, and give an example where $f$ never takes the value $0$.

### Reference

<?reference?>
