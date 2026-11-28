---
title: Division, real values and finite sums in ENNReal
kind: api
modules:
  - Mathlib.Basic.ENNReal.Inv
  - Mathlib.Basic.ENNReal.Real
  - Mathlib.Basic.ENNReal.Action
  - Mathlib.Basic.ENNReal.BigOperators
  - Mathlib.Basic.ENNReal.Lemmas
  - Mathlib.Data.ENNReal.Inv
  - Mathlib.Data.ENNReal.Real
  - Mathlib.Data.ENNReal.Action
  - Mathlib.Data.ENNReal.BigOperators
  - Mathlib.Data.ENNReal.Lemmas
explains:
  E2: [ENNReal.mul_inv_cancel, ENNReal.inv_le_inv, ENNReal.mul_inv, ENNReal.div_eq_top_iff, ENNReal.le_div_iff_mul_le, ENNReal.exists_inv_nat_lt, ENNReal.mul_iSup, ENNReal.trichotomy, ENNReal.sum_eq_top, ENNReal.toReal_sum]
  E1: auto
families: []
requires: [V02.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Division, real values and finite sums in ENNReal

### Overview

The first section of this chapter builds `ℝ≥0∞`, its addition, its multiplication and its order. This section treats the operations that come after them. The modules hold the inverse $a \mapsto a^{-1}$ with $0^{-1} = \infty$ and $\infty^{-1} = 0$, the division $a / b = a \cdot b^{-1}$, the powers with an integer exponent, and the maps `ENNReal.toReal` and `ENNReal.toNNReal` back to the finite numbers. They also hold the scalar actions of `ℝ≥0` and the finite sums and products.

Measure theory uses these lemmas all the time: a measure, the integral of a nonnegative function and an exponent $p$ of $L^p$ are all in `ℝ≥0∞`. Each lemma of this section has one of two forms. It holds with no hypothesis, because the conventions for $0$ and $\infty$ make it true in all cases. Or it needs hypotheses such as `a ≠ 0` and `a ≠ ⊤` that remove the bad cases.

### The library around it

#### The inverse and the division

`Mathlib.Basic.ENNReal.Basic` defines the inverse as $a^{-1} = \inf \{ b : 1 \leq a b \}$, and $a / b = a \cdot b^{-1}$. So $0^{-1} = \infty$, because $1 \leq 0 \cdot b$ holds for no $b$ and the infimum of the empty set is $\infty$. Also $\infty^{-1} = 0$, because $1 \leq \infty \cdot b$ for each $b \neq 0$. These are `ENNReal.inv_zero` and `ENNReal.inv_top`. The module `Mathlib.Basic.ENNReal.Inv` makes `ℝ≥0∞` a `DivInvOneMonoid` with an `InvolutiveInv`, so `inv_inv` gives $(a^{-1})^{-1} = a$. For a finite $r \neq 0$ the inverse agrees with the inverse of `ℝ≥0`: this is `ENNReal.coe_inv`. The hypothesis is needed, because $0^{-1} = 0$ in `ℝ≥0`.

**Theorem.** If $a \neq 0$ and $a \neq \infty$, then $a \cdot a^{-1} = 1$.

*Proof.* Write $a = r$ with $r \in [0, \infty)$ and $r \neq 0$. Then $a^{-1} = r^{-1}$ by `ENNReal.coe_inv`, and $a \cdot a^{-1} = r r^{-1} = 1$ in `ℝ≥0`. $\square$

This is `ENNReal.mul_inv_cancel`. The two hypotheses are necessary: $0 \cdot 0^{-1} = 0 \cdot \infty = 0$ and $\infty \cdot \infty^{-1} = \infty \cdot 0 = 0$. The cancellation lemmas `ENNReal.div_self`, `ENNReal.mul_div_cancel_right`, `ENNReal.div_mul_cancel` and `ENNReal.mul_inv_cancel_left` take the hypotheses `≠ 0` and `≠ ⊤` on the element that cancels.

**Theorem.** If $a \leq b$, then $b^{-1} \leq a^{-1}$. So $a^{-1} \leq b^{-1}$ if and only if $b \leq a$.

*Proof.* Let $a \leq b$. If $1 \leq a c$, then $1 \leq b c$. So the set $\{ c : 1 \leq a c \}$ is a subset of $\{ c : 1 \leq b c \}$, and the infimum of the larger set is smaller: $b^{-1} \leq a^{-1}$. For the converse, apply this to $b^{-1} \leq a^{-1}$ and use $(a^{-1})^{-1} = a$. $\square$

This is `ENNReal.inv_le_inv`, with the strict form `ENNReal.inv_lt_inv` and the monotonicity `ENNReal.inv_strictAnti`. The inverse is an order isomorphism from `ℝ≥0∞` to its order dual, `OrderIso.invENNReal`. So the inverse sends a supremum to an infimum: `ENNReal.inv_iSup` and `ENNReal.inv_iInf`.

**Theorem.** $(a b)^{-1} = a^{-1} b^{-1}$, if $a \neq 0$ or $b \neq \infty$, and if $a \neq \infty$ or $b \neq 0$.

*Proof.* If $a$ and $b$ are finite and not $0$, this is the rule of `ℝ≥0`. If $b = \infty$, then $a \neq 0$ and both sides are $0$. If $b = 0$, then $a \neq \infty$ and both sides are $\infty$. The cases $a = \infty$ and $a = 0$ are the same. $\square$

This is `ENNReal.mul_inv`. The hypotheses remove one bad case: $a = 0$ and $b = \infty$, where $(0 \cdot \infty)^{-1} = 0^{-1} = \infty$ but $0^{-1} \cdot \infty^{-1} = \infty \cdot 0 = 0$. The lemmas `ENNReal.inv_div` and `ENNReal.div_mul` have hypotheses of the same shape: two disjunctions, one for each bad product $0 \cdot \infty$.

`ENNReal.div_top` gives $a / \infty = 0$, `ENNReal.zero_div` gives $0 / a = 0$, and `ENNReal.div_zero` gives $a / 0 = \infty$ for $a \neq 0$. The lemma `ENNReal.top_div` says that $\infty / a$ is $0$ for $a = \infty$ and $\infty$ otherwise.

**Theorem.** $a / b = \infty$ if and only if $a \neq 0$ and $b = 0$, or $a = \infty$ and $b \neq \infty$.

*Proof.* $a / b = a \cdot b^{-1}$. A product is $\infty$ exactly when one factor is $\infty$ and the other factor is not $0$. Now $b^{-1} = \infty$ if and only if $b = 0$, and $b^{-1} \neq 0$ if and only if $b \neq \infty$. $\square$

This is `ENNReal.div_eq_top_iff`. The companions are `ENNReal.div_eq_zero_iff` ($a / b = 0$ if and only if $a = 0$ or $b = \infty$) and `ENNReal.div_pos_iff`. The lemma `ENNReal.div_ne_top` is a rule of the tactic `finiteness`, so a goal `a / b ≠ ⊤` often closes with it.

#### Inequalities with a quotient

The rule "multiply both sides by $b$" has the following form.

**Theorem.** If $b \neq 0$ or $c \neq 0$, and $b \neq \infty$ or $c \neq \infty$, then $a \leq c / b$ if and only if $a b \leq c$.

*Proof.* If $b$ is finite and not $0$, multiplication by $b$ is an order isomorphism with inverse the multiplication by $b^{-1}$, and the claim follows. If $b = 0$, then $c \neq 0$, so $c / 0 = \infty$ and both sides are true. If $b = \infty$, then $c \neq \infty$, so $c / \infty = 0$, and both sides say $a = 0$. $\square$

This is `ENNReal.le_div_iff_mul_le`. When $b = c = 0$ it fails: $1 \leq 0 / 0 = 0$ is false, but $1 \cdot 0 \leq 0$ is true. The family has these members.

| Lean name | Statement |
|---|---|
| `ENNReal.div_le_iff` | for $b \neq 0, \infty$: $a / b \leq c \iff a \leq c b$ |
| `ENNReal.div_le_iff_le_mul` | $a / b \leq c \iff a \leq c b$, with two disjunctions as hypotheses |
| `ENNReal.div_lt_iff` | $c / b < a \iff c < a b$, with two disjunctions as hypotheses |
| `ENNReal.div_le_of_le_mul` | $a \leq b c \implies a / c \leq b$, with no hypothesis |
| `ENNReal.mul_le_of_le_div` | $a \leq b / c \implies a c \leq b$, with no hypothesis |
| `ENNReal.div_le_div` | $a \leq b$ and $d \leq c$ imply $a / c \leq b / d$ |

The lemmas `ENNReal.div_le_div` and `ENNReal.inv_le_inv'` carry the attribute `gcongr`, so the tactic `gcongr` uses them.

Halves have their own lemmas: `ENNReal.add_halves` gives $a / 2 + a / 2 = a$ with no hypothesis, `ENNReal.inv_two_add_inv_two` gives $2^{-1} + 2^{-1} = 1$, and `ENNReal.half_lt_self` gives $a / 2 < a$ for $a \neq 0, \infty$. The division distributes over the addition with no hypothesis: `ENNReal.add_div`.

#### Archimedean facts and integer powers

**Theorem.** If $a \neq 0$, there is $n \in \mathbb{N}$ with $1 / n < a$.

*Proof.* If $a = \infty$, take $n = 1$, since $1 < \infty$. Otherwise $a = r$ with $r > 0$ real. The Archimedean property gives $n > 1 / r$. Then $n \geq 1$ and $1 / n < r$. $\square$

This is `ENNReal.exists_inv_nat_lt`. It and `ENNReal.exists_inv_two_pow_lt` are the tools of the $\varepsilon$ arguments of measure theory. To prove $x \leq y$, it is enough to prove $r \leq y$ for each finite $r < x$: this is `ENNReal.le_of_forall_nnreal_lt`.

Because `ℝ≥0∞` is a `DivInvOneMonoid`, the power $a^n$ makes sense for $n \in \mathbb{Z}$, with $a^{-n} = (a^n)^{-1}$ (`ENNReal.zpow_neg`). The lemmas `ENNReal.zero_zpow_def` and `ENNReal.top_zpow_def` give the values at $0$ and $\infty$. For instance $0^n = \infty$ for $n < 0$. The rule $a^{m + n} = a^m a^n$ is `ENNReal.zpow_add`, and it needs $a \neq 0$ and $a \neq \infty$.

#### Order isomorphisms and suprema

An element is a unit exactly when it is not $0$ and not $\infty$: `ENNReal.isUnit_iff`. For such an $a$, the multiplication by $a$ is an order isomorphism, `ENNReal.mulLeftOrderIso` and `ENNReal.mulRightOrderIso`. Two more order isomorphisms compare `ℝ≥0∞` with a bounded interval. `ENNReal.orderIsoIicOneBirational` is the map $x \mapsto (x^{-1} + 1)^{-1}$ from $[0, \infty]$ onto $[0, 1]$, with the inverse $y \mapsto (y^{-1} - 1)^{-1}$. `ENNReal.orderIsoUnitIntervalBirational` is the same map with values in the real interval $[0, 1]$.

**Theorem.** For each family $(f_i)$ and each $a$, $a \cdot \sup_i f_i = \sup_i a f_i$.

*Proof.* If $a = 0$, both sides are $0$. If $a$ is a unit, the multiplication by $a$ is an order isomorphism, and an order isomorphism keeps suprema. Let $a = \infty$. If each $f_i = 0$, both sides are $0$. Otherwise some $f_i \neq 0$, so $\sup_i f_i \neq 0$ and $\infty \cdot f_i = \infty$, and both sides are $\infty$. $\square$

This is `ENNReal.mul_iSup`, with `ENNReal.iSup_mul` and `ENNReal.iSup_div`. The infimum is harder, because $\infty \cdot \inf_i f_i$ can be $0$ when no $f_i$ is $0$. So `ENNReal.mul_iInf_of_ne` needs $a \neq 0, \infty$, and the general form `ENNReal.mul_iInf'` states exactly the cases that it excludes.

#### The maps to ℝ and ℝ≥0

The module `Mathlib.Basic.ENNReal.Real` studies `ENNReal.toReal`, `ENNReal.toNNReal` and `ENNReal.ofReal` with the operations. The rule is simple. A map from `ℝ≥0∞` sends $\infty$ to the junk value $0$, so a lemma that adds or compares needs `≠ ⊤`. A map from `ℝ` sends each $r \leq 0$ to $0$, so a lemma about `ENNReal.ofReal` needs `0 ≤ p`.

| Lean name | Statement |
|---|---|
| `ENNReal.toReal_add` | for $a, b \neq \infty$: $\operatorname{toReal}(a + b) = \operatorname{toReal} a + \operatorname{toReal} b$ |
| `ENNReal.toReal_mul` | $\operatorname{toReal}(a b) = \operatorname{toReal} a \cdot \operatorname{toReal} b$, with no hypothesis |
| `ENNReal.toReal_inv` | $\operatorname{toReal}(a^{-1}) = (\operatorname{toReal} a)^{-1}$, with no hypothesis |
| `ENNReal.toReal_le_toReal` | for $a, b \neq \infty$: $\operatorname{toReal} a \leq \operatorname{toReal} b \iff a \leq b$ |
| `ENNReal.ofReal_add` | for $p, q \geq 0$: $\operatorname{ofReal}(p + q) = \operatorname{ofReal} p + \operatorname{ofReal} q$ |
| `ENNReal.ofReal_mul` | for $p \geq 0$: $\operatorname{ofReal}(p q) = \operatorname{ofReal} p \cdot \operatorname{ofReal} q$ |
| `ENNReal.ofReal_le_ofReal_iff` | for $q \geq 0$: $\operatorname{ofReal} p \leq \operatorname{ofReal} q \iff p \leq q$ |
| `ENNReal.ofReal_le_iff_le_toReal` | for $b \neq \infty$: $\operatorname{ofReal} a \leq b \iff a \leq \operatorname{toReal} b$ |

The multiplication needs no hypothesis because both sides are $0$ when a factor is $\infty$ or $0$. The same holds for the inverse and the division (`ENNReal.toReal_div`, `ENNReal.toNNReal_inv`): $\operatorname{toReal}(0^{-1}) = \operatorname{toReal}(\infty) = 0 = 0^{-1}$ in `ℝ`. So `ENNReal.toRealHom` and `ENNReal.toNNRealHom` are maps of monoids with zero, but not maps of additive monoids.

**Theorem.** Each $p \in [0, \infty]$ satisfies $p = 0$, or $p = \infty$, or $0 < \operatorname{toReal} p$.

*Proof.* If $p$ is finite, $p = r$ with $r \geq 0$, and $\operatorname{toReal} p = r$. Either $r = 0$ or $r > 0$. $\square$

This is `ENNReal.trichotomy`. It is the usual first step for an exponent $p$ of $L^p$. Under the instance `Fact (1 ≤ p)`, `ENNReal.dichotomy` gives $p = \infty$ or $1 \leq \operatorname{toReal} p$, and `ENNReal.toReal_pos_iff_ne_top` gives $0 < \operatorname{toReal} p$ for each finite $p$. The module also gives a `positivity` extension for `ENNReal.ofReal`.

#### Scalar actions

The module `Mathlib.Basic.ENNReal.Action` restricts actions. If `ℝ≥0∞` acts on a type $M$ by a `MulAction`, then `ℝ≥0` acts on $M$ through the cast, and `ENNReal.smul_def` says $c \bullet x = (c : [0, \infty]) \bullet x$. The same holds for a `DistribMulAction`, a `Module` and an `Algebra`. So a module over `ℝ≥0∞` is also a module over `ℝ≥0`. In `ℝ≥0∞` itself, `ENNReal.smul_top` gives $c \bullet \infty = \infty$ for $c \neq 0$, and `ENNReal.toReal_smul` moves the action through `ENNReal.toReal`.

#### Finite sums and products

The module `Mathlib.Basic.ENNReal.BigOperators` treats `Finset.sum` and `Finset.prod` in `ℝ≥0∞`. The cast from `ℝ≥0` commutes with them: `ENNReal.ofNNReal_finsetSum` and `ENNReal.ofNNReal_finsetProd`, both `simp` and `norm_cast` lemmas.

**Theorem.** A finite sum $\sum_{i \in s} f_i$ is $\infty$ if and only if some $f_i$ with $i \in s$ is $\infty$.

*Proof.* Induction on $s$. The empty sum is $0 \neq \infty$. For $s \cup \{j\}$ with $j \notin s$, the sum is $f_j + \sum_{i \in s} f_i$, and a sum of two terms is $\infty$ if and only if one term is $\infty$ (`ENNReal.add_eq_top`). $\square$

This is `ENNReal.sum_eq_top`, with `ENNReal.sum_lt_top` and `ENNReal.sum_ne_top`. For products only one direction holds with no other hypothesis, `ENNReal.prod_ne_top`, because a product with a factor $0$ is $0$.

**Theorem.** If $f_i \neq \infty$ for each $i \in s$, then $\operatorname{toReal} \sum_{i \in s} f_i = \sum_{i \in s} \operatorname{toReal} f_i$.

*Proof.* Induction on $s$. In the step, $\sum_{i \in s} f_i$ is finite by the theorem above, so `ENNReal.toReal_add` applies. $\square$

This is `ENNReal.toReal_sum`, with `ENNReal.toNNReal_sum`. For products, `ENNReal.toReal_prod` needs no hypothesis, as for `ENNReal.toReal_mul`. In the other direction, `ENNReal.ofReal_sum_of_nonneg` needs $f_i \geq 0$.

The division distributes over a finite sum: `ENNReal.sum_div`. The general lemma `Finset.sum_div` does not apply, because `ℝ≥0∞` is not a `DivisionSemiring`. The inverse of a product is the product of the inverses under a pairwise condition: `ENNReal.prod_inv_distrib`. A finite sum commutes with a directed supremum: `ENNReal.finsetSum_iSup_of_monotone` gives $\sum_{a \in s} \sup_n f_a(n) = \sup_n \sum_{a \in s} f_a(n)$ for monotone $f_a$. This is the finite case of the monotone convergence theorem.

The small module `Mathlib.Basic.ENNReal.Lemmas` proves that the cast from `ℝ≥0` commutes with `Set.indicator` and with `Finset.sup`: `ENNReal.coe_indicator` and `ENNReal.coe_finset_sup`.

The modules `Mathlib.Data.ENNReal.Inv`, `Mathlib.Data.ENNReal.Real`, `Mathlib.Data.ENNReal.Action`, `Mathlib.Data.ENNReal.BigOperators` and `Mathlib.Data.ENNReal.Lemmas` are deprecated redirects to the modules of the same last name in the folder `Mathlib/Basic/ENNReal`.

#### Common errors

1. A general lemma of fields does not apply. The type `ℝ≥0∞` is not a field and not a `DivisionSemiring`, so `div_self`, `mul_inv_cancel₀` and `Finset.sum_div` fail. Use the protected names `ENNReal.div_self`, `ENNReal.mul_inv_cancel` and `ENNReal.sum_div`, and give the hypotheses `≠ 0` and `≠ ⊤`.
2. A lemma on `ENNReal.toReal` is used without its hypothesis. $\operatorname{toReal}(\infty + 1) = 0$, but $\operatorname{toReal} \infty + 1 = 1$. Before `ENNReal.toReal_add` or `ENNReal.toReal_sum`, prove that the terms are finite, for example with `finiteness`.
3. The cast lemma for sums has a new name. The names `ENNReal.coe_finsetSum` and `ENNReal.coe_finsetProd` are deprecated. Use `ENNReal.ofNNReal_finsetSum` and `ENNReal.ofNNReal_finsetProd`.

### Exercises

1. (A) Compute $\infty / \infty$, $0 / 0$, $\infty / 0$ and $1 / \infty$ in $[0, \infty]$, and name the lemma for each value.
2. (A) Show that $(0 \cdot \infty)^{-1} \neq 0^{-1} \cdot \infty^{-1}$, and explain which hypothesis of `ENNReal.mul_inv` fails.
3. (B) Show that $x \mapsto (x^{-1} + 1)^{-1}$ is the map $x \mapsto x / (1 + x)$ for finite $x$, that it sends $\infty$ to $1$, and that $y \mapsto (y^{-1} - 1)^{-1}$ is its inverse on $[0, 1]$.
4. (B) Prove that $\infty \cdot \inf_n 2^{-n} = 0$ but $\inf_n (\infty \cdot 2^{-n}) = \infty$. Deduce that `ENNReal.mul_iInf_of_ne` needs the hypothesis $a \neq \infty$.
5. (B) Prove $\operatorname{toReal}(a / b) = \operatorname{toReal} a / \operatorname{toReal} b$ for all $a, b$, including the cases $a$ or $b$ in $\{0, \infty\}$.
6. (C) Let $f_1, \dots, f_n \in [0, \infty]$. Prove that $\prod_i f_i^{-1} = (\prod_i f_i)^{-1}$ when no $f_i$ is $0$, and find $f_1, f_2$ for which the equality fails.

### Reference

<?reference?>
