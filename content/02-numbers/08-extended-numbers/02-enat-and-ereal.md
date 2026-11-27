---
title: "ENat and EReal"
kind: theory
modules:
  - Mathlib.Data.ENat.Defs
  - Mathlib.Data.ENat.Basic
  - Mathlib.Data.ENat.Monoid
  - Mathlib.Data.EReal.Basic
  - Mathlib.Data.EReal.Operations
explains:
  E3: [ENat, EReal]
  E2: [ENat.toNat, ENat.toNat_add, ENat.top_mul, EReal.toReal, EReal.bot_add, EReal.top_add_of_ne_bot]
  E1: auto
families: []
requires: [V02.C05, V02.C07]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V02/C08/Examples.lean
  - MathlibHandbook/V02/C08/Exercises.lean
  - MathlibHandbook/V02/C08/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## ENat and EReal

### Overview

The previous section added a top element $\infty$ to $[0, \infty)$. The same step works for other ordered types. Mathlib adds a top element to `ℕ` to get `ENat` (notation `ℕ∞`), and adds a bottom and a top element to `ℝ` to get `EReal`. The type `ℕ∞` holds the size of a set that can be infinite, and `EReal` holds the limits of real sequences that can go to $+\infty$ or $-\infty$. The rules for the new elements follow from the general types `WithTop` and `WithBot`.

### Definitions

**Definition (WithTop and WithBot).** For an ordered type $\alpha$, $\operatorname{WithTop}(\alpha) = \alpha \cup \{\top\}$ with $a < \top$ for each $a \in \alpha$. In the same way $\operatorname{WithBot}(\alpha) = \alpha \cup \{\bot\}$ with $\bot < a$. An addition on $\alpha$ extends to $\operatorname{WithTop}(\alpha)$ by $a + \top = \top + a = \top$.

::: mathlib
`WithTop` · `Mathlib.Order.TypeTags`

`WithTop α` is `Option α`: `⊤` is `none` and the cast `↑a` is `some a`. The general lemmas `WithTop.coe_add`, `WithTop.add_top` and `WithTop.coe_ne_top` hold for each `α`, and a proof by cases uses `WithTop.recTopCoe`. The type `WithBot` is the same with `⊥`.

<?decl WithTop?>
:::

**Definition (Extended natural numbers).** $\mathbb{N}_\infty = \operatorname{WithTop}(\mathbb{N})$. The multiplication extends by $m \cdot \infty = \infty \cdot m = \infty$ for $m \neq 0$ and $0 \cdot \infty = 0$. The truncated subtraction gives $\infty \mathbin{\dot -} n = \infty$ for finite $n$ and $a \mathbin{\dot -} \infty = 0$.

::: mathlib
`ENat` · `Mathlib.Data.ENat.Defs`

`ENat` is `WithTop ℕ`, a canonically ordered commutative semiring and a complete linear order. The cast from `ℕ` has the lemmas `ENat.natCast_ne_top`, `ENat.natCast_lt_top` and `ENat.natCast_add`. The old names with `coe` in place of `natCast`, such as `ENat.coe_ne_top`, are deprecated.

<?decl ENat?>
:::

**Definition (toNat).** $\operatorname{toNat}(n) = n$ for finite $n$, and $\operatorname{toNat}(\infty) = 0$.

::: mathlib
`ENat.toNat` · `Mathlib.Data.ENat.Basic`

The junk value at `⊤` is $0$. So `ENat.toNat_eq_zero` says `n.toNat = 0 ↔ n = 0 ∨ n = ⊤`, and `ENat.natCast_toNat` needs `n ≠ ⊤`. The lemma `ENat.toNat_natCast` needs no hypothesis.

<?decl ENat.toNat?>
:::

**Definition (Extended reals).** $\overline{\mathbb{R}} = \mathbb{R} \cup \{-\infty, +\infty\}$ with $-\infty < x < +\infty$ for each real $x$. The addition extends by $x + (+\infty) = +\infty$ for $x \neq -\infty$ and $x + (-\infty) = -\infty$ for each $x$, so $(-\infty) + (+\infty) = -\infty$. The multiplication extends by the rule of signs, with $0 \cdot (\pm\infty) = 0$. The map toReal sends $\pm\infty$ to $0$.

::: mathlib
`EReal` · `Mathlib.Data.EReal.Basic`

`EReal` is `WithBot (WithTop ℝ)`, a complete linear order with `⊥` for $-\infty$ and `⊤` for $+\infty$. It is an additive commutative monoid, but its multiplication is not distributive, so it is not a semiring. The negation `EReal.instNeg` swaps `⊥` and `⊤`.

<?decl EReal?>
:::

::: mathlib
`EReal.toReal` · `Mathlib.Data.EReal.Basic`

Both junk values are $0$: `EReal.toReal_top` and `EReal.toReal_bot`. So `EReal.toReal_add` has four hypotheses, `x ≠ ⊤`, `x ≠ ⊥`, `y ≠ ⊤` and `y ≠ ⊥`.

<?decl EReal.toReal?>
:::

### Theorems and proofs

**Theorem (toNat and sums).** For finite $m, n \in \mathbb{N}_\infty$, $\operatorname{toNat}(m + n) = \operatorname{toNat}(m) + \operatorname{toNat}(n)$. The equation fails for $m = \infty$, $n = 1$.

*Proof.* For finite $m$ and $n$, $m + n$ is the natural number $m + n$, and toNat is the identity on finite values. For $m = \infty$ and $n = 1$, the left side is $\operatorname{toNat}(\infty) = 0$ and the right side is $0 + 1 = 1$. $\square$

::: mathlib
`ENat.toNat_add` · `Mathlib.Data.ENat.Basic`

The two hypotheses `m ≠ ⊤` and `n ≠ ⊤` are necessary by the theorem. The lemma `ENat.toNat_sub` needs only `n ≠ ⊤`.

<?decl ENat.toNat_add?>
:::

**Theorem (toNat and products).** For all $a, b \in \mathbb{N}_\infty$, $\operatorname{toNat}(a b) = \operatorname{toNat}(a) \operatorname{toNat}(b)$.

*Proof.* If $a$ and $b$ are finite, both sides are $a b$. Suppose $a = \infty$ (the case $b = \infty$ is the same). If $b = 0$, then $a b = 0$ and both sides are $0$. If $b \neq 0$, then $a b = \infty$, so the left side is $0$, and the right side is $0 \cdot \operatorname{toNat}(b) = 0$. $\square$

::: mathlib
`ENat.top_mul` · `Mathlib.Data.ENat.Monoid`

`⊤ * m = ⊤` for `m ≠ 0`, and `ENat.mul_top` is the mirror form. The theorem above is `ENat.toNat_mul`, with no hypotheses.

<?decl ENat.top_mul?>
:::

**Theorem (Sums in EReal).** For $x \in \overline{\mathbb{R}}$, $(-\infty) + x = -\infty$, and $(+\infty) + x = +\infty$ if $x \neq -\infty$.

*Proof.* $\overline{\mathbb{R}} = \operatorname{WithBot}(\operatorname{WithTop}(\mathbb{R}))$. The addition of WithBot sends each sum with $\bot$ to $\bot$, so $(-\infty) + x = -\infty$. If $x \neq -\infty$, then $x$ is in $\operatorname{WithTop}(\mathbb{R})$, and there the addition sends each sum with $\top$ to $\top$. $\square$

::: mathlib
`EReal.bot_add` · `Mathlib.Data.EReal.Operations`

The lemma has no hypothesis, so `⊥ + ⊤ = ⊥`. The mirror form is `EReal.add_bot`.

<?decl EReal.bot_add?>
:::

::: mathlib
`EReal.top_add_of_ne_bot` · `Mathlib.Data.EReal.Operations`

The hypothesis `x ≠ ⊥` is necessary by `EReal.bot_add`. The equivalence form is `EReal.top_add_iff_ne_bot`.

<?decl EReal.top_add_of_ne_bot?>
:::

**Remark.** The choice $(-\infty) + (+\infty) = -\infty$ is a convention. It makes the addition total and keeps the monoid laws. The value $x - (+\infty) = -\infty$ holds for each $x$, as `EReal.sub_top` says.

### Examples

**Example (Cardinals of sets).** `Set.encard s : ℕ∞` is the number of elements of a finite set and `⊤` for an infinite set. The function `Set.ncard` is its composition with `ENat.toNat`, so `Set.ncard` of an infinite set is the junk value $0$. In the same way `ENat.card α` and `Nat.card α` are the two forms for a type.

**Example (Multiplicity).** `emultiplicity a b : ℕ∞` is the largest $k$ such that $a^k$ divides $b$, and `⊤` if each power divides $b$. For example, each power of $2$ divides $0$, so the emultiplicity of $2$ in $0$ is `⊤`. The function `multiplicity` is the ℕ form, with a junk value when each power divides $b$.

**Example (Products in EReal).** By the rule of signs, $(-\infty)(-\infty) = +\infty$ (`EReal.bot_mul_bot`) and $(+\infty)(-\infty) = -\infty$ (`EReal.top_mul_bot`). Distributivity fails: $(+\infty) \cdot (1 + (-1)) = 0$, but $(+\infty) \cdot 1 + (+\infty) \cdot (-1) = (+\infty) + (-\infty) = -\infty$.

**Counterexample (Cancellation fails in ℕ∞).** In $\mathbb{N}_\infty$, $3 + \infty = \infty = 5 + \infty$, but $3 \neq 5$. So $a + c = b + c$ gives $a = b$ only for $c \neq \infty$, and the cancellation lemmas of `ℕ∞` carry this hypothesis. In the same way $2 \cdot \infty = 3 \cdot \infty$, so multiplication cancels only by a finite nonzero factor. The order also changes: in $\mathbb{N}$ the set $\mathbb{N}$ has no upper bound, but in $\mathbb{N}_\infty$ each set has a least upper bound, and the supremum of the finite values is $\infty$. The order of $\mathbb{N}_\infty$ is still a well order: a nonempty subset that contains a finite value has the least element of its finite part, and the set $\{\infty\}$ has the least element $\infty$. So the minimum of a set of sizes or of multiplicities always exists.

**Example (Lean).** The map `ENat.toNat` is the identity on `ℕ`, with the junk value $0$ at `⊤`.

<?lean MathlibHandbook/V02/C08/Examples.lean#enat?>

### The library around it

`Mathlib.Data.ENat.Defs` has `ENat` and `Mathlib.Data.ENat.Basic` has `ENat.toNat`, the cast lemmas and `ENat.sub_top`. `Mathlib.Data.ENat.Monoid` has the multiplication lemmas, and `Mathlib.Data.ENat.Lattice` has the suprema. `Mathlib.Data.EReal.Basic` has `EReal`, its order and its casts, such as `EReal.coe_toReal` and `EReal.coe_ennreal_top`. `Mathlib.Data.EReal.Operations` has the addition, the subtraction and the multiplication, and `Mathlib.Data.EReal.Inv` has the inverse. The general lemmas of `WithTop` and `WithBot` are in the volume on order.

### Exercises

1. (A) Give the values of `(⊤ : ℕ∞).toNat`, `(⊤ : ℕ∞) - 5`, `(3 : ℕ∞) - ⊤` and `(0 : ℕ∞) * ⊤`. *Hint.* Use the rules of the definition.
2. (A) Give the value of `Set.ncard (Set.univ : Set ℕ)`. *Hint.* The set is infinite.
3. (B) Show that $\operatorname{toNat}(m) \leq \operatorname{toNat}(n)$ for $m \leq n$ and $n \neq \infty$. Give a counterexample with $n = \infty$. *Hint.* Take $m = 1$.
4. (B) Show that the addition of $\overline{\mathbb{R}}$ is associative. *Hint.* If a term is $-\infty$, both sides are $-\infty$. Otherwise check the cases with $+\infty$.
5. (C) Show that $x - x = 0$ in $\overline{\mathbb{R}}$ if and only if $x$ is finite. *Hint.* Compute $(+\infty) - (+\infty)$ and $(-\infty) - (-\infty)$ with the rules for sums.
6. (L) Prove that `(n.toNat : ℕ∞) = n` for `n ≠ ⊤`. The solution is `enat_coe_toNat`.

### Notes and history

The extended real line is the two point compactification of $\mathbb{R}$, and Rudin, *Real and Complex Analysis*, uses it for the upper and lower limits. Mathlib first had the type `PartENat` and later used `ENat = WithTop ℕ` in its place, and the `coe` lemmas of `ENat` were renamed with `natCast`. The type `EReal` came with the measure theory library.

### Reference

<?reference?>
