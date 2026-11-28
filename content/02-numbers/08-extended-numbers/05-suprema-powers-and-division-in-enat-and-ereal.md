---
title: Suprema, powers and division in ENat and EReal
kind: api
modules:
  - Mathlib.Data.ENat.Lattice
  - Mathlib.Data.ENat.BigOperators
  - Mathlib.Data.ENat.Pow
  - Mathlib.Data.ENat.SuccOrder
  - Mathlib.Basic.Real.ENatENNReal
  - Mathlib.Data.Real.ENatENNReal
  - Mathlib.Data.EReal.Inv
  - Mathlib.Data.EReal.BigOperators
  - Mathlib.Data.EReal.DedekindCut
explains:
  E2: [ENat.sSup_eq_top_of_infinite, ENat.exists_eq_iSup_of_lt_top, ENat.epow_def, ENat.epow_add, ENat.toENNReal, EReal.inv, EReal.sign_eq_and_abs_eq_iff_eq, EReal.dedekindCutOrderIso]
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

## Suprema, powers and division in ENat and EReal

### Overview

The section on `ENat` and `EReal` builds the two types and their addition and multiplication. This section collects the next layer of the library. For `ℕ∞` it gives the complete lattice, with suprema and infima of families and their interaction with the arithmetic, the finite sums and products, a power $x^y$ with an exponent in `ℕ∞`, and the cast to `ℝ≥0∞`. For `EReal` it gives the absolute value and the sign, the inverse and the division, finite sums, and the theorem that `EReal` is the Dedekind completion of `ℚ`.

A reader needs these results when a size or a dimension can be infinite. The cardinality `Set.encard` of a set and the cardinality `ENat.card` of a type take values in `ℕ∞`, and their suprema and sums need the lemmas below. `EReal` appears for limits superior and inferior of real sequences.

### The library around it

#### The complete lattice ℕ∞

The module `Mathlib.Data.ENat.Lattice` derives the instance `instCompleteLinearOrderENat`: each set of `ℕ∞` has a supremum and an infimum. It also gives `instCompleteLinearOrderWithBotENat` for `WithBot ℕ∞`. The module restates the lemmas of `WithTop` with the cast `Nat.cast` in place of `WithTop.some`, so a proof does not leave the simp normal form.

The first family compares a supremum of casts with `⊤`. For $f : \iota \to \mathbb{N}$, `ENat.iSup_natCast_eq_top` says $\sup_i f(i) = \top$ if and only if $f$ is not bounded above, and `ENat.iSup_natCast_ne_top` and `ENat.iSup_natCast_lt_top` give the other forms. The infimum of casts is `⊤` exactly when the index type is empty: `ENat.iInf_natCast_eq_top`, `ENat.iInf_natCast_ne_top`, `ENat.iInf_natCast_lt_top` and `ENat.iInf_eq_top_of_isEmpty`. The forms with `coe` in the name, such as `ENat.iSup_natCast_eq_top`, state the same facts. The cast commutes with a bounded supremum and with an infimum over a nonempty index: `ENat.natCast_iSup`, `ENat.natCast_sSup`, `ENat.natCast_iInf` and `ENat.natCast_sInf`. The supremum of all casts is `⊤`: this is `ENat.iSup_natCast`.

The order of `ℕ` is a well order with no infinite bounded sets. So suprema and infima in `ℕ∞` behave better than in `ℝ≥0∞`.

**Lemma.** An infinite set $s \subseteq \mathbb{N}_\infty$ has supremum $\top$.

*Proof.* If $\top \in s$, the claim holds. Otherwise $s$ is the image of an infinite set $t \subseteq \mathbb{N}$. An infinite set of natural numbers has no upper bound, because a set bounded by $n$ is a subset of $\{0, \ldots, n\}$. So the supremum of the casts is $\top$. $\square$

This is `ENat.sSup_eq_top_of_infinite`. The contrapositive is `ENat.finite_of_sSup_lt_top`.

**Lemma.** If $\iota$ is nonempty and $\sup_i f(i) < \top$, then $f(i) = \sup_i f(i)$ for some $i$.

*Proof.* All values are finite and bounded, so the range of $f$ is a nonempty bounded set of natural numbers. It has a greatest element, and this element is the supremum. $\square$

This is `ENat.exists_eq_iSup_of_lt_top`, with the form `ENat.sSup_mem_of_nonempty_of_lt_top` for sets and `ENat.exists_eq_iSup₂_of_lt_top` for two indices. An infimum over a nonempty index is always attained, finite or not: `ENat.exists_eq_iInf`. The lemmas `ENat.iInf_eq_zero`, `ENat.iSup_eq_zero`, `ENat.sSup_eq_zero`, `ENat.sInf_eq_zero` and `ENat.iInf_eq_natCast_iff` describe the special values.

The second family moves addition and multiplication through suprema and infima. The names follow the pattern of `ℝ≥0∞`.

| Lean name | Statement |
|---|---|
| `ENat.mul_iSup` | $a \cdot \sup_i f(i) = \sup_i a f(i)$ |
| `ENat.iSup_mul` | $(\sup_i f(i)) \cdot a = \sup_i f(i) a$ |
| `ENat.mul_iInf` | $a \cdot \inf_i f(i) = \inf_i a f(i)$ for $\iota$ nonempty |
| `ENat.mul_iInf_of_ne` | the same for $a \neq 0$ and any $\iota$ |
| `ENat.add_iSup` | $a + \sup_i f(i) = \sup_i (a + f(i))$ for $\iota$ nonempty |
| `ENat.iInf_add` | $\inf_i f(i) + a = \inf_i (f(i) + a)$ |
| `ENat.sub_iSup` | $a - \sup_i f(i) = \inf_i (a - f(i))$ for $a \neq \top$ and $\iota$ nonempty |
| `ENat.sub_iInf` | $a - \inf_i f(i) = \sup_i (a - f(i))$ |
| `ENat.iSup_add_iSup` | $\sup f + \sup g = \sup_i (f(i) + g(i))$ if each pair is dominated by a diagonal term |
| `ENat.iSup_add_iSup_of_monotone` | the same for monotone $f$, $g$ on a directed order |

The forms with `sSup`, `sInf`, `biSup` and `iInf₂` exist for each line, for example `ENat.mul_sSup`, `ENat.add_sSup` and `ENat.add_biSup`. The hypothesis "$\iota$ nonempty" in `ENat.add_iSup` is necessary: for the empty family the left side is $a$ and the right side is $0$. The lemma `ENat.mul_iSup` needs no such hypothesis, because $a \cdot 0 = 0$.

#### Finite sums and products in ℕ∞

The module `Mathlib.Data.ENat.BigOperators` treats `Finset.sum` and `Finset.prod`. A finite sum is `⊤` if and only if a term is `⊤`: this is the simp lemma `ENat.sum_eq_top`, with `ENat.sum_ne_top` and `ENat.sum_lt_top`. A product of finite terms is finite: `ENat.prod_ne_top` and `ENat.prod_lt_top`. The map `ENat.toNat` commutes with products in all cases (`ENat.toNat_prod`), because a factor `⊤` gives `toNat` value $0$ on both sides, but it commutes with sums only when all terms are finite (`ENat.toNat_sum`). Strict inequalities between sums are `ENat.sum_lt_sum_of_nonempty` and `ENat.exists_le_of_sum_le`. A finite sum commutes with a directed supremum: `ENat.sum_iSup` and `ENat.sum_iSup_of_monotone`. It commutes with a directed infimum over a nonempty index: `ENat.iInf_sum`.

#### Powers with an exponent in ℕ∞

The module `Mathlib.Data.ENat.Pow` defines $x^y$ for $x, y \in \mathbb{N}_\infty$, through the instance `ENat.instPow`. The definition follows cardinal arithmetic: $x^y$ is the number of maps from a set of size $y$ to a set of size $x$. For finite $y$ it is the usual power. For $y = \top$, `ENat.epow_def` gives

$$x^\top = \begin{cases} 0 & x = 0, \\ 1 & x = 1, \\ \top & x \geq 2. \end{cases}$$

A lemma about this power has `epow` in its name, to tell it from the power `x ^ n` with `n : ℕ`. The lemma `ENat.epow_natCast` is the bridge: $x^{(n : \mathbb{N}_\infty)} = x^n$. It is a `simp` and `norm_cast` lemma.

| Lean name | Statement |
|---|---|
| `ENat.epow_zero`, `ENat.epow_one` | $x^0 = 1$, $x^1 = x$ |
| `ENat.zero_epow`, `ENat.zero_epow_top` | $0^y = 0$ for $y \neq 0$ |
| `ENat.one_epow` | $1^y = 1$ |
| `ENat.top_epow`, `ENat.top_epow_top` | $\top^y = \top$ for $y \neq 0$ |
| `ENat.epow_top` | $x^\top = \top$ for $1 < x$ |
| `ENat.epow_eq_zero_iff` | $x^y = 0 \iff x = 0 \wedge y \neq 0$ |
| `ENat.epow_eq_one_iff` | $x^y = 1 \iff x = 1 \vee y = 0$ |
| `ENat.epow_add` | $x^{y + z} = x^y x^z$ |
| `ENat.mul_epow` | $(x y)^z = x^z y^z$ |
| `ENat.epow_mul` | $x^{y z} = (x^y)^z$ |
| `ENat.epow_left_mono`, `ENat.epow_right_mono` | monotone in $x$, and in $y$ for $x \neq 0$ |

**Lemma.** $x^{y + z} = x^y x^z$ for all $x, y, z \in \mathbb{N}_\infty$.

*Proof.* If $y$ and $z$ are finite, this is the rule for natural exponents. Otherwise $y + z = \top$, and the case $y = \top$ is enough by symmetry. For $x = 0$ both sides are $0$, since $0^\top = 0$. For $x = 1$ both sides are $1$. For $x \geq 2$ the left side is $\top$, and the right side is $\top \cdot x^z$ with $x^z \geq 1$, which is $\top$. $\square$

#### The cast from ℕ∞ to ℝ≥0∞

The module `Mathlib.Basic.Real.ENatENNReal` defines `ENat.toENNReal` as `ENat.map Nat.cast`: it sends $n$ to $n$ and $\top$ to $\infty$. It is a coercion, so `(n : ℝ≥0∞)` for `n : ℕ∞` elaborates to it. The map is bundled as an order embedding, `ENat.toENNRealOrderEmbedding`, and as a ring homomorphism, `ENat.toENNRealRingHom`. The lemmas are `norm_cast` lemmas with the prefix `ENat.toENNReal_`: `ENat.toENNReal_top`, `ENat.toENNReal_coe`, `ENat.toENNReal_inj`, `ENat.toENNReal_le`, `ENat.toENNReal_lt`, `ENat.toENNReal_add`, `ENat.toENNReal_mul`, `ENat.toENNReal_pow`, `ENat.toENNReal_min`, `ENat.toENNReal_max`, and `ENat.toENNReal_sub` for the truncated subtraction. The lemma `ENat.toENNReal_eq_top` says that the cast is $\infty$ only at $\top$. Since the cast is strictly monotone (`ENat.toENNReal_strictMono`), an inequality in `ℝ≥0∞` between casts gives one in `ℕ∞`, and `norm_cast` does this step.

#### Successors in ℕ∞

The module `Mathlib.Data.ENat.SuccOrder` has no declarations. It imports `Mathlib.Order.SuccPred.ENat`, which gives the instance `instSuccOrderENat` with `Order.succ_eq_add_one`, $\operatorname{succ}(m) = m + 1$, and lemmas such as `ENat.lt_add_one_iff` and `ENat.add_one_le_iff`, which need $m \neq \top$.

#### Absolute value, sign and the multiplication of EReal

The module `Mathlib.Data.EReal.Inv` defines `EReal.abs : EReal → ℝ≥0∞`. It sends a real $x$ to $|x|$ and both $\bot$ and $\top$ to $\infty$ (`EReal.abs_def`, `EReal.abs_top`, `EReal.abs_bot`). The sign is the general function `SignType.sign`, with `EReal.sign_top`, `EReal.sign_bot` and `EReal.sign_coe`. Both maps are multiplicative: `EReal.abs_mul` and `EReal.sign_mul`. A value is the product of its sign and its absolute value (`EReal.sign_mul_abs`), and the pair determines it.

**Lemma.** For $x, y \in \overline{\mathbb{R}}$, $x = y$ if and only if $|x| = |y|$ and $\operatorname{sign} x = \operatorname{sign} y$.

*Proof.* The sign is $-1$, $0$ or $1$. Sign $0$ gives $x = 0$. Sign $1$ and $|x| = \infty$ give $x = \top$, and sign $1$ and a finite $|x|$ give the real $x = |x|$. Sign $-1$ is the same with $\bot$ and $-|x|$. So the pair determines $x$. $\square$

This is `EReal.sign_eq_and_abs_eq_iff_eq`. It proves the associativity of the multiplication of `EReal` without a long case analysis on the infinite values: the sign and the absolute value of both sides of $(x y) z = x (y z)$ agree, because sign and absolute value are multiplicative and the multiplications of `SignType` and `ℝ≥0∞` are associative. The result is the instance `EReal.instCommMonoidWithZero`. The instances `EReal.instPosMulMono` and `EReal.instMulPosMono` say that multiplication by a nonnegative element is monotone, and `EReal.le_iff_sign` compares two values through their signs and absolute values.

#### Inverse and division in EReal

The inverse `EReal.inv` sends a real $x$ to $x^{-1}$ and both $\bot$ and $\top$ to $0$. It also sends $0$ to $0$, as in a field of Mathlib. With this choice the rule $(a b)^{-1} = a^{-1} b^{-1}$ holds for all $a$ and $b$ (`EReal.mul_inv`), and so does $(-a)^{-1} = -a^{-1}$ (`EReal.inv_neg`). The instance `EReal.instDivInvMonoid` defines $a / b = a \cdot b^{-1}$. But `EReal.inv_inv` needs $a \neq \bot$ and $a \neq \top$, because $(\top^{-1})^{-1} = 0^{-1} = 0$. The inverse is never infinite: `EReal.bot_lt_inv` and `EReal.inv_lt_top`.

The lemmas on division state the values at the special points and the cancellation rules.

| Lean name | Statement |
|---|---|
| `EReal.div_zero`, `EReal.zero_div` | $a / 0 = 0$, $0 / a = 0$ |
| `EReal.div_top`, `EReal.div_bot` | $a / \top = 0$, $a / \bot = 0$ |
| `EReal.top_div_of_pos_ne_top` | $\top / a = \top$ for $0 < a < \top$ |
| `EReal.div_eq_top_iff` | $a / b = \top$ exactly for $a = \top$, $0 < b < \top$ or $a = \bot$, $\bot < b < 0$ |
| `EReal.div_self` | $a / a = 1$ for $a \notin \{\bot, 0, \top\}$ |
| `EReal.div_mul_cancel` | $(a / b) b = a$ for $b \notin \{\bot, 0, \top\}$ |
| `EReal.div_le_iff_le_mul` | $a / b \leq c \iff a \leq b c$ for $0 < b < \top$ |
| `EReal.lt_div_iff` | $a < c / b \iff a b < c$ for $0 < b < \top$ |
| `EReal.div_le_div_right_of_nonneg` | division by $c \geq 0$ is monotone |
| `EReal.div_lt_div_right_of_neg` | division by $\bot < c < 0$ reverses strict inequalities |
| `EReal.add_div_of_nonneg_right` | $(a + b)/c = a/c + b/c$ for $c \geq 0$ |

The cast lemmas `EReal.coe_inv`, `EReal.coe_div`, `EReal.coe_pow` and `EReal.coe_ennreal_pow` connect with `ℝ` and `ℝ≥0∞`. The module also extends the tactic `positivity` to $a^{-1}$ and $a / b$ in `EReal`.

The module `Mathlib.Data.EReal.BigOperators` has five lemmas on finite sums. The cast from `ℝ` commutes with sums (`EReal.coe_finsetSum`). Multiplication distributes over a sum when the terms are nonnegative (`EReal.mul_sum_of_nonneg`, `EReal.sum_mul_of_nonneg`) or when the factor is nonnegative and finite (`EReal.mul_sum_of_nonneg_of_ne_top`, `EReal.sum_mul_of_nonneg_of_ne_top`). Some hypothesis is needed, because $\top \cdot (1 + (-1)) = 0$ but $\top \cdot 1 + \top \cdot (-1) = \top + \bot = \bot$.

#### EReal as the Dedekind completion of ℚ

A Dedekind cut of $\mathbb{Q}$ in the sense of `DedekindCut ℚ` is a pair $(L, U)$ of sets with $U$ the set of upper bounds of $L$ and $L$ the set of lower bounds of $U$. The pairs $(\emptyset, \mathbb{Q})$ and $(\mathbb{Q}, \emptyset)$ are cuts. So the completion has a least and a greatest element, and it is $\overline{\mathbb{R}}$, not $\mathbb{R}$.

The module `Mathlib.Data.EReal.DedekindCut` gives the order isomorphism `EReal.dedekindCutOrderIso : DedekindCut ℚ ≃o EReal`. A cut $A$ goes to the supremum of its lower set, `EReal.dedekindCutOrderIso_apply_eq_sSup`, or equally to the infimum of its upper set, `EReal.dedekindCutOrderIso_apply_eq_sInf`. The inverse sends $x$ to $(\{q : q \leq x\}, \{q : x \leq q\})$: these are `EReal.left_dedekindCutOrderIso_symm_apply` and `EReal.right_dedekindCutOrderIso_symm_apply`. The two sets are polars of each other by `EReal.upperBounds_setOfPred_ratCast_le` and `EReal.lowerBounds_setOfPred_le_ratCast`, which use the density of $\mathbb{Q}$ in $\overline{\mathbb{R}}$. The cut `DedekindCut.principal q` goes to the cast of $q$: `EReal.dedekindCutOrderIso_principal`. So the construction of the reals by Dedekind cuts gives the same ordered set as the construction by Cauchy sequences, once the two infinite points are added.

#### Common errors

1. A supremum in `ℕ∞` over an empty family is $0$, and an infimum is $\top$. So `ENat.add_iSup` and `ENat.mul_iInf` need `[Nonempty ι]`, and `ENat.mul_iInf_of_ne` replaces it by $a \neq 0$.
2. For `x y : ℕ∞` the term `x ^ y` uses `ENat.instPow`, and its lemmas have `epow` in the name. For `n : ℕ` the term `x ^ n` is the monoid power. A rewrite with `ENat.epow_natCast` passes from one to the other.
3. In `EReal` the inverse of $\top$ is $0$, so $\top / \top = 0$, and `EReal.div_self` and `EReal.inv_inv` need the hypotheses $a \neq \bot$ and $a \neq \top$. The inverse in `ℝ≥0∞` sends $0$ to $\infty$ instead: do not transfer a lemma from `ℝ≥0∞` by analogy.

### Exercises

1. (A) Compute $2^\top$, $1^\top$, $0^\top$ and $\top^0$ in `ℕ∞` with the lemmas of the table.
2. (A) Compute $\top / 2$, $\bot / 2$, $3 / \top$ and $(-2)^{-1}$ in `EReal`.
3. (B) Prove that $\sup_n f(n) = \top$ for an injective $f : \mathbb{N} \to \mathbb{N}$, with `ENat.sSup_eq_top_of_infinite` or `ENat.iSup_natCast_eq_top`.
4. (B) Prove `ENat.mul_epow` from `ENat.epow_def` by cases on $z$.
5. (B) Show that $(x y)^{-1} = x^{-1} y^{-1}$ in `EReal` fails if $0^{-1}$ is defined as $\top$, and give $x$ and $y$ for which it fails.
6. (C) Describe the cut $(L, U)$ of $\mathbb{Q}$ that `EReal.dedekindCutOrderIso` sends to $\sqrt{2}$, and prove that $L \cup U = \mathbb{Q}$ while $L \cap U = \emptyset$.

### Reference

<?reference?>
