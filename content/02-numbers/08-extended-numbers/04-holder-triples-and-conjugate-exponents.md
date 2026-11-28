---
title: Hölder triples and conjugate exponents
kind: api
modules:
  - Mathlib.Basic.ENNReal.Holder
  - Mathlib.Basic.Real.ConjExponents
  - Mathlib.Data.ENNReal.Holder
  - Mathlib.Data.Real.ConjExponents
explains:
  E2: [ENNReal.HolderTriple, ENNReal.HolderConjugate, ENNReal.HolderTriple.le, ENNReal.HolderTriple.holderConjugate_div_div, ENNReal.conjExponent, ENNReal.holderTriple_coe_iff, Real.HolderConjugate.conjugate_eq, Real.HolderConjugate.mul_eq_add]
  E1: auto
families: []
requires: [V02.C05, V02.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Hölder triples and conjugate exponents

### Overview

Hölder's inequality states $\|f g\|_r \leq \|f\|_p \|g\|_q$ when the exponents satisfy $\frac1p + \frac1q = \frac1r$. The case $r = 1$ is the most common one: then $p$ and $q$ are *conjugate exponents*, for example $p = q = 2$, or $p = 1$ and $q = \infty$. The inequality itself lives in the volumes on analysis and measure theory. The two modules of this section hold only the arithmetic of the exponents. This arithmetic is short, but a proof about $L^p$ spaces uses it again and again, so the library states it once.

The exponents of an $L^p$ space are elements of `ℝ≥0∞`, because $p = \infty$ is allowed. The first module, `Mathlib.Basic.ENNReal.Holder`, treats exponents in `ℝ≥0∞` and uses the rules for $0^{-1} = \infty$ and $\infty^{-1} = 0$ from the first section of this chapter. The second module, `Mathlib.Basic.Real.ConjExponents`, treats exponents in `ℝ` and `ℝ≥0`, where all exponents are finite and positive, and gives the bridges between the three types.

### The library around it

#### Hölder triples in ℝ≥0∞

The class `ENNReal.HolderTriple p q r` has one field, `ENNReal.HolderTriple.inv_add_inv_eq_inv`, which states $p^{-1} + q^{-1} = r^{-1}$. The lemma `ENNReal.holderTriple_iff` unfolds the class. The abbreviation `ENNReal.HolderConjugate p q` is `ENNReal.HolderTriple p q 1`, and `ENNReal.holderConjugate_iff` gives $p^{-1} + q^{-1} = 1$.

The class is a class, not a plain predicate, for a reason in measure theory. With an instance `[HolderTriple p q r]`, Lean can find the exponent $r$ of a product $f \cdot g$ with $f \in L^p$ and $g \in L^q$. So the third argument is marked `semiOutParam`: Lean searches for it from $p$ and $q$. The library uses this for the scalar multiplication of `MeasureTheory.Lp`, through `MeasureTheory.MemLp.smul`.

The instances of the module cover the common cases.

| Lean name | Statement |
|---|---|
| `ENNReal.HolderTriple.symm` | a triple $(p, q, r)$ gives the triple $(q, p, r)$ |
| `ENNReal.HolderTriple.instInfty` | $(p, \infty, p)$ is a triple, because $\infty^{-1} = 0$ |
| `ENNReal.HolderTriple.instZero` | $(p, 0, 0)$ is a triple, because $0^{-1} = \infty$ |
| `ENNReal.HolderConjugate.instTwoTwo` | $2$ and $2$ are conjugate |
| `ENNReal.HolderConjugate.instOneInfty` | $1$ and $\infty$ are conjugate |
| `ENNReal.HolderConjugate.one_top` | $1$ and $\infty$ are conjugate (a lemma) |
| `ENNReal.HolderConjugate.top_one` | $\infty$ and $1$ are conjugate (a lemma) |

The lemma `ENNReal.HolderTriple.of` gives the triple $(p, q, (p^{-1} + q^{-1})^{-1})$ for each $p$ and $q$. It is not an instance, so that Lean does not choose this value of $r$ when a simpler value exists.

The lemmas in the namespace `ENNReal.HolderTriple` take $p$, $q$ and $r$ as explicit arguments and the triple as an instance. The forms `ENNReal.HolderTriple.inv_eq`, `ENNReal.HolderTriple.one_div_add_one_div`, `ENNReal.HolderTriple.one_div_eq` and `ENNReal.HolderTriple.inv_inv_add_inv` restate the field. The lemma `ENNReal.HolderTriple.unique` says that $r$ is unique, because inversion is injective on `ℝ≥0∞`.

**Lemma.** If $(p, q, r)$ is a Hölder triple in $[0, \infty]$, then $r \leq p$.

*Proof.* $r^{-1} = p^{-1} + q^{-1} \geq p^{-1}$. Inversion reverses the order of $[0, \infty]$ (`ENNReal.inv_le_inv`), so $r \leq p$. $\square$

This is `ENNReal.HolderTriple.le`, and `ENNReal.HolderTriple.inv_le_inv` is the form $p^{-1} \leq r^{-1}$. Subtraction needs care, because `ℝ≥0∞` has truncated subtraction and $\infty - \infty = 0$. The lemma `ENNReal.HolderTriple.inv_sub_inv_eq_inv` gives $r^{-1} - q^{-1} = p^{-1}$ under the hypothesis $r \neq 0$, and `ENNReal.HolderTriple.inv_sub_inv_eq_inv'` gives the same result under $q \neq 0$. From it, `ENNReal.HolderTriple.unique_of_ne_zero` says that $r \neq 0$ and $p$ fix $q$.

**Lemma.** If $(p, q, r)$ is a Hölder triple and $0 < r < \infty$, then $p / r$ and $q / r$ are conjugate.

*Proof.* $(p/r)^{-1} + (q/r)^{-1} = r p^{-1} + r q^{-1} = r (p^{-1} + q^{-1}) = r r^{-1} = 1$. The last step needs $r \neq 0$ and $r \neq \infty$. $\square$

This is `ENNReal.HolderTriple.holderConjugate_div_div`. It reduces Hölder's inequality for a general $r$ to the conjugate case.

#### Conjugate exponents in ℝ≥0∞

For conjugate $p$ and $q$, the triple lemma gives $1 \leq p$. This is `ENNReal.HolderConjugate.one_le`, with the corollaries `ENNReal.HolderConjugate.pos` and `ENNReal.HolderConjugate.ne_zero`. The other lemmas of the namespace `ENNReal.HolderConjugate` are these.

| Lean name | Statement |
|---|---|
| `ENNReal.HolderConjugate.inv_add_inv_eq_one` | $p^{-1} + q^{-1} = 1$ |
| `ENNReal.HolderConjugate.one_sub_inv` | $1 - p^{-1} = q^{-1}$ |
| `ENNReal.HolderConjugate.unique` | the conjugate of $p$ is unique |
| `ENNReal.HolderConjugate.ne_top_iff_ne_one` | $p \neq \infty \iff q \neq 1$ |
| `ENNReal.HolderConjugate.lt_top_iff_one_lt` | $p < \infty \iff 1 < q$ |
| `ENNReal.HolderConjugate.sub_one_mul_inv` | $(p - 1) p^{-1} = q^{-1}$ for $p \neq \infty$ |
| `ENNReal.HolderConjugate.mul_eq_add` | $p q = p + q$ |
| `ENNReal.HolderConjugate.div_conj_eq_sub_one` | $p / q = p - 1$ |

The conjugate exponent of $p \in [1, \infty]$ is `ENNReal.conjExponent p`, defined as $1 + (p - 1)^{-1}$. This formula is chosen because it gives the right value at the ends: $1 + 0^{-1} = \infty$ for $p = 1$, and $1 + \infty^{-1} = 1$ for $p = \infty$. The formula $p / (p - 1)$ gives $\infty / \infty = \infty \cdot 0 = 0$ at $p = \infty$, which is wrong, because the conjugate of $\infty$ is $1$. The lemma `ENNReal.HolderConjugate.conjExponent` says that $p$ and `ENNReal.conjExponent p` are conjugate for $1 \leq p$, and `ENNReal.HolderConjugate.conjExponent_eq` and `ENNReal.HolderConjugate.conj_eq` say that each conjugate of $p$ is this value. In $L^p$ theory the hypothesis $1 \leq p$ often comes as an instance `[Fact (1 ≤ p)]`, and the instance `ENNReal.HolderConjugate.instConjExponentOfFactLeOfNat` uses it. The equivalence `ENNReal.isConjExponent_iff_eq_conjExponent` and the symmetry `ENNReal.isConjExponent_comm` have names with a different pattern from the rest of the module.

Three lemmas build conjugate pairs from a split of $1$. `ENNReal.HolderConjugate.inv_inv` says that $a + b = 1$ makes $a^{-1}$ and $b^{-1}$ conjugate. `ENNReal.HolderConjugate.inv_one_sub_inv` and `ENNReal.HolderConjugate.one_sub_inv_inv` treat $b = 1 - a$ for $a \leq 1$, and `ENNReal.HolderConjugate.inv_one_sub_inv'` treats $a \geq 1$.

#### Hölder triples in ℝ and ℝ≥0

In `ℝ` the exponents are finite, and the definition must exclude the junk value $0^{-1} = 0$. So `Real.HolderTriple p q r` is a structure with three fields: `Real.HolderTriple.inv_add_inv_eq_inv`, `Real.HolderTriple.left_pos` and `Real.HolderTriple.right_pos`. It is a plain predicate, not a class, and a proof uses a hypothesis `h : p.HolderTriple q r` with dot notation. The constructor is `Real.HolderTriple.mk` and the unfolding lemma is `Real.holderTriple_iff`. The abbreviation `Real.HolderConjugate p q` is `Real.HolderTriple p q 1`. The type `ℝ≥0` has the same API in the namespace `NNReal`: `NNReal.HolderTriple`, `NNReal.HolderConjugate`, `NNReal.conjExponent`, and each lemma below with `NNReal` in place of `Real`.

The positivity lemmas come in two families. The names without a prime are about $p$: `Real.HolderTriple.pos`, `Real.HolderTriple.nonneg`, `Real.HolderTriple.ne_zero`, `Real.HolderTriple.inv_pos` and the forms with `one_div`. The names with a prime are about $r$: `Real.HolderTriple.pos'`, `Real.HolderTriple.ne_zero'` and so on. For $q$, apply the lemma to `h.symm`, which is `Real.HolderTriple.symm`. The lemma `Real.HolderTriple.all_pos` gives the three facts at once and is a rule of `grind`.

Since $q^{-1} > 0$, the inequality of the triple is strict: `Real.HolderTriple.lt` gives $r < p$, and `Real.HolderTriple.inv_lt_inv` gives $p^{-1} < r^{-1}$. The subtraction `Real.HolderTriple.inv_sub_inv_eq_inv` and the division `Real.HolderTriple.holderConjugate_div_div` need no side hypothesis, because $r > 0$ follows from the definition. The lemma `Real.HolderTriple.of_pos` builds the triple $(p, q, (p^{-1} + q^{-1})^{-1})$ for $p, q > 0$.

#### Conjugate exponents in ℝ

The lemma `Real.holderConjugate_iff` gives the usual definition: $p$ and $q$ are conjugate if and only if $1 < p$ and $p^{-1} + q^{-1} = 1$. The positivity of $q$ follows: $q^{-1} = 1 - p^{-1} > 0$.

**Lemma.** If $p$ and $q$ are conjugate real exponents, then $q = p / (p - 1)$ and $p q = p + q$.

*Proof.* $q^{-1} = 1 - p^{-1} = (p - 1)/p$, and $p - 1 > 0$, so $q = p/(p-1)$. Multiply $p^{-1} + q^{-1} = 1$ by $p q$ to get $q + p = p q$. $\square$

These are `Real.HolderConjugate.conjugate_eq` and `Real.HolderConjugate.mul_eq_add`. The definition `Real.conjExponent p` is $p/(p-1)$, and `Real.HolderConjugate.conjExponent_eq` says that it equals $q$. The other lemmas are these.

| Lean name | Statement |
|---|---|
| `Real.HolderConjugate.sub_one_pos` | $0 < p - 1$ |
| `Real.HolderConjugate.sub_one_ne_zero` | $p - 1 \neq 0$ |
| `Real.HolderConjugate.one_sub_inv` | $1 - p^{-1} = q^{-1}$ |
| `Real.HolderConjugate.inv_sub_one` | $p^{-1} - 1 = -q^{-1}$ |
| `Real.HolderConjugate.sub_one_mul_conj` | $(p - 1) q = p$ |
| `Real.HolderConjugate.div_conj_eq_sub_one` | $p / q = p - 1$ |
| `Real.HolderConjugate.two_two` | $2$ and $2$ are conjugate |
| `Real.HolderConjugate.conjExponent` | $p$ and $p/(p-1)$ are conjugate for $1 < p$ |
| `Real.holderConjugate_iff_eq_conjExponent` | for $1 < p$, $q$ is conjugate to $p$ if and only if $q = p/(p-1)$ |
| `Real.holderConjugate_comm` | the relation is symmetric |
| `Real.holderConjugate_one_div` | $a, b > 0$ and $a + b = 1$ make $1/a$ and $1/b$ conjugate |

The lemmas `Real.HolderConjugate.inv_inv`, `Real.HolderConjugate.inv_one_sub_inv` and `Real.HolderConjugate.one_sub_inv_inv` are the real forms of the lemmas on splits of $1$. They need $0 < a$, and $a < 1$ when $1 - a$ appears.

#### Bridges between the three types

A proof often starts with real exponents and ends in `ℝ≥0∞`, or the reverse. The module gives transfer lemmas in each direction.

1. From `ℝ` to `ℝ≥0`: `Real.HolderTriple.toNNReal` and `Real.HolderConjugate.toNNReal`.
2. Between `ℝ≥0` and `ℝ`: `NNReal.holderTriple_coe_iff` and `NNReal.holderConjugate_coe_iff` are `simp` and `norm_cast` lemmas, with the one way forms `NNReal.HolderTriple.coe` and `NNReal.HolderConjugate.coe`.
3. From `ℝ` to `ℝ≥0∞`: `Real.HolderTriple.ennrealOfReal`, `Real.HolderConjugate.ennrealOfReal`, and `Real.HolderConjugate.inv_add_inv_ennreal` for the equation itself.
4. Between `ℝ≥0` and `ℝ≥0∞`: `ENNReal.holderTriple_coe_iff` and `ENNReal.holderConjugate_coe_iff`, with `NNReal.HolderTriple.coe_ennreal` and `NNReal.HolderConjugate.coe_ennreal`. Also `ENNReal.coe_conjExponent` says that the two conjugate exponents agree for $1 < p$.
5. From `ℝ≥0∞` back to `ℝ` or `ℝ≥0`: `ENNReal.HolderTriple.toReal`, `ENNReal.HolderTriple.toReal_iff`, `ENNReal.HolderTriple.of_toReal`, the forms with `toNNReal`, and the same names in the namespace `ENNReal.HolderConjugate`. The lemma `ENNReal.HolderConjugate.toReal_of_ne_top` needs only $p \neq \infty$ and $q \neq \infty$.

The lemma `ENNReal.holderTriple_coe_iff` has the hypothesis $r \neq 0$. The reason is the junk value. In `ℝ≥0` no triple has $r = 0$, because $p^{-1} + q^{-1} > 0$. In `ℝ≥0∞` the triple $(0, q, 0)$ exists, because $0^{-1} = \infty$. So for $p = 0$ the two sides differ.

These modules are the input of Young's inequality `Real.young_inequality`, of the finite Hölder inequality `Real.inner_le_Lp_mul_Lq`, and of the Hölder inequality for integrals `ENNReal.lintegral_mul_le_Lp_mul_Lq`.

#### Common errors

1. The real and the extended forms differ in their hypotheses. In `ℝ≥0∞` the pair $(1, \infty)$ is conjugate and $(p, 0, 0)$ is a triple. In `ℝ` the exponent $\infty$ does not exist and $p = 0$ is excluded by `Real.HolderTriple.left_pos`. A lemma from one namespace does not apply to the other: use a bridge lemma.
2. `ENNReal.HolderTriple` is a class and its lemmas take the exponents explicitly, as in `ENNReal.HolderConjugate.one_le p q`. `Real.HolderTriple` is a structure, and its lemmas take the proof, as in `h.pos`. A call of the wrong form fails to elaborate.
3. The conjugate exponent in `ℝ≥0∞` is $1 + (p - 1)^{-1}$, not $p / (p - 1)$. A rewrite with `ENNReal.HolderConjugate.conj_eq` gives the first form. Use `ENNReal.coe_conjExponent` to pass to the formula of `NNReal.conjExponent`.

### Exercises

1. (A) Show that $3$ and $3/2$ are conjugate real exponents, and compute `Real.conjExponent 4`.
2. (A) Show that $(2, 2, 1)$, $(4, 4, 2)$ and $(p, \infty, p)$ are Hölder triples in $[0, \infty]$.
3. (B) Let $p$ and $q$ be conjugate in $[0, \infty]$. Prove that $p = \infty$ if and only if $q = 1$, with `ENNReal.HolderConjugate.one_sub_inv`.
4. (B) Prove `Real.HolderConjugate.div_conj_eq_sub_one` from `Real.HolderConjugate.mul_eq_add`.
5. (B) Give $p, q \in \mathbb{R}_{\geq 0}$ with $p^{-1} + q^{-1} = 1$ in `ℝ≥0` that do not form a Hölder conjugate pair, and explain which field fails.
6. (C) Prove that if $(p, q, r)$ and $(r, s, t)$ are Hölder triples in $[0, \infty]$, then $(p, (q^{-1} + s^{-1})^{-1}, t)$ is a Hölder triple, and give the instance or lemma of the module that builds the middle exponent.

### Reference

<?reference?>
