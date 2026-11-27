---
title: Absolute values and their topologies
kind: theory
modules:
  - Mathlib.Analysis.AbsoluteValue.Equivalence
explains:
  E3: [AbsoluteValue.IsEquiv, AbsoluteValue.isEquiv_iff_lt_one_iff, AbsoluteValue.isEquiv_iff_exists_rpow_eq, AbsoluteValue.isEquiv_iff_isHomeomorph, AbsoluteValue.denseRange_algebraMap_pi]
  E2: [AbsoluteValue.IsEquiv.refl, AbsoluteValue.IsEquiv.symm, AbsoluteValue.IsEquiv.trans, AbsoluteValue.IsEquiv.lt_one_iff, AbsoluteValue.IsEquiv.le_one_iff, AbsoluteValue.IsEquiv.isNontrivial_congr, AbsoluteValue.isEquiv_trivial_iff_eq_trivial, AbsoluteValue.isEquiv_of_lt_one_imp, AbsoluteValue.exists_one_lt_lt_one_of_not_isEquiv, AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv, AbsoluteValue.IsEquiv.log_div_log_pos, AbsoluteValue.IsEquiv.isEmbedding_equivWithAbs]
  E1: auto
families: []
requires: [V06, V13, V15, V14.C02, V14.C03]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Absolute values and their topologies

### Overview

The field $\mathbb{Q}$ carries the usual absolute value and, for each prime $p$, the $p$-adic absolute value. Each one makes $\mathbb{Q}$ a metric space, and the completions are $\mathbb{R}$ and $\mathbb{Q}_p$. This section asks when two absolute values on a field give the same topology. The answer is the theorem of this section: they do exactly when one is a positive power of the other, and exactly when they order the elements of the field in the same way. The section ends with the weak approximation theorem, which says that absolute values that are not equivalent are independent.

### Definitions

An *absolute value* on a field $F$ is a map $v : F \to \mathbb{R}$ with $v(x) \ge 0$, $v(x) = 0$ exactly when $x = 0$, $v(xy) = v(x)v(y)$ and $v(x + y) \le v(x) + v(y)$. Then $v(1) = 1$ and $v(x^{-1}) = v(x)^{-1}$ for $x \ne 0$. The *trivial* absolute value has $v(x) = 1$ for every $x \ne 0$. An absolute value is *nontrivial* when some $x \ne 0$ has $v(x) \ne 1$; then some $x$ has $v(x) > 1$ and some has $v(x) < 1$, since $v(x^{-1}) = v(x)^{-1}$.

An absolute value gives $F$ the metric $d(x, y) = v(x - y)$, and the field operations are continuous for it, so $F$ is a topological field in the sense of Chapter 2. The trivial absolute value gives the discrete topology.

Two absolute values $v$ and $w$ on $F$ are *equivalent* when $v(x) \le v(y) \iff w(x) \le w(y)$ for all $x, y \in F$.

::: mathlib
`AbsoluteValue.IsEquiv` · `Mathlib.Analysis.AbsoluteValue.Equivalence`

The definition `v.IsEquiv w := ∀ x y, v x ≤ v y ↔ w x ≤ w y`, for absolute values `v w : AbsoluteValue R S` with values in an ordered semiring `S`. It is an equivalence relation, by `AbsoluteValue.IsEquiv.refl`, `.symm` and `.trans`. The structure `AbsoluteValue R S` is in `Mathlib.Algebra.Order.AbsoluteValue.Basic`. The field $F$ with the metric of `v` is the type synonym `WithAbs v` of `Mathlib.Analysis.Normed.Ring.WithAbs`, so two absolute values on one field give two different types, and `WithAbs.congr v w (RingEquiv.refl F)` is the identity map between them.

<?decl AbsoluteValue.IsEquiv?>
<?decl WithAbs?>
:::

Many texts define equivalence by the condition that $v$ and $w$ define the same topology, or that $w = v^c$ for some $c > 0$. The theorems below show that the three definitions agree for real absolute values. Mathlib chose the order condition because it makes sense for values in any ordered semiring.

### Theorems and proofs

**Theorem (Equivalence by the unit ball).** Let $v$ and $w$ be absolute values on $F$. Then $v$ and $w$ are equivalent exactly when $v(x) < 1 \iff w(x) < 1$ for every $x \in F$.

*Proof.* If $v$ and $w$ are equivalent, then $v(x) < 1 = v(1)$ exactly when $w(x) < w(1) = 1$, by the order condition with $y = 1$ in its strict form. For the converse, first $v(z) \le 1 \iff w(z) \le 1$: for $z = 0$ both sides hold, and for $z \ne 0$, $v(z) \le 1$ is the negation of $v(z^{-1}) < 1$, and the same holds for $w$. Now let $x, y \in F$. If $y = 0$, then $v(x) \le 0$ and $w(x) \le 0$ both say $x = 0$. If $y \ne 0$, then $v(x) \le v(y) \iff v(x/y) \le 1 \iff w(x/y) \le 1 \iff w(x) \le w(y)$. $\square$

::: mathlib
`AbsoluteValue.isEquiv_iff_lt_one_iff` · `Mathlib.Analysis.AbsoluteValue.Equivalence`

The statement `v.IsEquiv w ↔ ∀ x, v x < 1 ↔ w x < 1`. A one-sided form is `AbsoluteValue.isEquiv_of_lt_one_imp`: if `v` is nontrivial and `v x < 1 → w x < 1` for every `x`, then `v.IsEquiv w`. The lemmas `AbsoluteValue.IsEquiv.lt_one_iff` and `.le_one_iff` use an equivalence in the other direction.

<?decl AbsoluteValue.isEquiv_iff_lt_one_iff?>
<?decl AbsoluteValue.isEquiv_of_lt_one_imp?>
:::

**Theorem (Equivalence and powers).** Let $v$ and $w$ be absolute values on $F$. Then $v$ and $w$ are equivalent exactly when there is $c > 0$ with $w(x) = v(x)^c$ for every $x$.

*Proof.* If $w = v^c$ with $c > 0$, then $t \mapsto t^c$ is strictly increasing on $[0, \infty)$, so $v$ and $w$ order $F$ in the same way. Conversely, let $v$ and $w$ be equivalent. Equivalence keeps the condition $v(x) = 1$, so if $v$ is trivial, then $w$ is trivial and $c = 1$ works. Otherwise choose $a$ with $v(a) > 1$; then $w(a) > 1$. Let $c = \log w(a) / \log v(a) > 0$.

Let $x \ne 0$ and $\alpha = \log v(x) / \log v(a)$, so that $v(x) = v(a)^{\alpha}$. Let $m/n$ be a rational number with $n > 0$. If $m/n > \alpha$, then $v(x)^n < v(a)^m$, so $v(x^n) < v(a^m)$, so $w(x^n) < w(a^m)$ by equivalence, and $w(x) < w(a)^{m/n}$. In the same way $m/n < \alpha$ gives $w(x) > w(a)^{m/n}$. Since the rationals are dense, $w(x) = w(a)^{\alpha}$. So $\log w(x) = \alpha \log w(a) = c \log v(x)$, and $w(x) = v(x)^c$. Both sides are $0$ at $x = 0$. $\square$

::: mathlib
`AbsoluteValue.isEquiv_iff_exists_rpow_eq` · `Mathlib.Analysis.AbsoluteValue.Equivalence`

The statement, for `v w : AbsoluteValue F ℝ` on a field: `v.IsEquiv w ↔ ∃ c : ℝ, 0 < c ∧ (fun x ↦ v x ^ c) = ⇑w`. The constant is the ratio of logarithms of the proof, and `AbsoluteValue.IsEquiv.log_div_log_pos` proves that it is positive.

<?decl AbsoluteValue.isEquiv_iff_exists_rpow_eq?>
<?decl AbsoluteValue.IsEquiv.log_div_log_pos?>
:::

**Theorem (Equivalence and topology).** Let $v$ and $w$ be absolute values on $F$. Then $v$ and $w$ are equivalent exactly when the identity map from $F$ with the metric of $v$ to $F$ with the metric of $w$ is a homeomorphism.

*Proof.* If $w = v^c$, then the ball $\{x : w(x - y) < r\}$ equals the ball $\{x : v(x - y) < r^{1/c}\}$, so the two metrics have the same open sets. Conversely, let the identity be a homeomorphism. For $x \in F$, the sequence $x^n$ tends to $0$ for $v$ exactly when $v(x) < 1$: if $v(x) < 1$, then $v(x^n) = v(x)^n \to 0$, and if $v(x) \ge 1$, then $v(x^n) \ge 1$ for every $n$. The same holds for $w$. A homeomorphism keeps convergent sequences, so $v(x) < 1 \iff x^n \to 0 \iff w(x) < 1$, and the first theorem gives the equivalence. $\square$

::: mathlib
`AbsoluteValue.isEquiv_iff_isHomeomorph` · `Mathlib.Analysis.AbsoluteValue.Equivalence`

The statement `v.IsEquiv w ↔ IsHomeomorph ⇑(WithAbs.congr v w (RingEquiv.refl F))` for real absolute values on a field. One direction is `AbsoluteValue.IsEquiv.isEmbedding_equivWithAbs`.

<?decl AbsoluteValue.isEquiv_iff_isHomeomorph?>
:::

**Theorem (Weak approximation).** Let $v_1, \dots, v_n$ be nontrivial absolute values on $F$, no two of them equivalent. Then the diagonal map $F \to \prod_j F_{v_j}$, where $F_{v_j}$ is $F$ with the metric of $v_j$, has dense image.

*Proof.* Step 1: for $n = 2$ there is $a$ with $v_1(a) > 1$ and $v_2(a) < 1$. Since $v_1$ is nontrivial and not equivalent to $v_2$, the one-sided form of the first theorem gives $b$ with $v_1(b) < 1$ and $v_2(b) \ge 1$. In the same way there is $c$ with $v_2(c) < 1$ and $v_1(c) \ge 1$. Then $a = c/b$ works.

Step 2: for each $i$ there is $a$ with $v_i(a) > 1$ and $v_j(a) < 1$ for $j \ne i$. Take $i = 1$ and use induction on $n$. Let $a$ work for $v_1, \dots, v_{n-1}$, and let $b$ work for the pair $v_1, v_n$ by Step 1. If $v_n(a) < 1$, then $a$ works. If $v_n(a) = 1$, then $a^m b$ works for $m$ large. If $v_n(a) > 1$, then $a^m b / (1 + a^m)$ works for $m$ large, since $a^m / (1 + a^m)$ tends to $1$ for $v_1$ and $v_n$ and to $0$ for the other $v_j$.

Step 3: let $u_m = a_i^m / (1 + a_i^m)$ with $a_i$ from Step 2. Then $u_m \to 1$ for $v_i$ and $u_m \to 0$ for $v_j$, $j \ne i$. Given $x_1, \dots, x_n \in F$, the elements $\sum_i x_i u_{i,m}$ tend to $x_j$ for each $v_j$. So every point of $F^n$ is a limit of the diagonal image, and $F^n$ is dense in the product. $\square$

::: mathlib
`AbsoluteValue.denseRange_algebraMap_pi` · `Mathlib.Analysis.AbsoluteValue.Equivalence`

The statement, for a finite index type `ι` and `v : ι → AbsoluteValue F ℝ` with `∀ i, (v i).IsNontrivial` and `Pairwise fun i j ↦ ¬(v i).IsEquiv (v j)`: `DenseRange ⇑(algebraMap F ((i : ι) → WithAbs (v i)))`. Steps 1 and 2 are `AbsoluteValue.exists_one_lt_lt_one_of_not_isEquiv` and `AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv`.

<?decl AbsoluteValue.denseRange_algebraMap_pi?>
<?decl AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv?>
:::

### Examples

**Example (The real and the p-adic absolute values).** On $\mathbb{Q}$, the usual absolute value $|\cdot|_\infty$ and the $p$-adic absolute value $|\cdot|_p$ are not equivalent: $|p|_\infty = p > 1$ and $|p|_p = 1/p < 1$. Two $p$-adic absolute values for $p \ne q$ are not equivalent: $|p|_p < 1$ and $|p|_q = 1$. By weak approximation, for any rationals $x_\infty, x_2, x_3$ and $\varepsilon > 0$ there is $y \in \mathbb{Q}$ with $|y - x_\infty|_\infty$, $|y - x_2|_2$ and $|y - x_3|_3$ all less than $\varepsilon$. The theorem of Ostrowski says that every nontrivial absolute value on $\mathbb{Q}$ is equivalent to exactly one of these.

::: mathlib
`Rat.AbsoluteValue.equiv_real_or_padic` · `Mathlib.NumberTheory.Ostrowski`

The theorem of Ostrowski for $\mathbb{Q}$. The absolute values are `Rat.AbsoluteValue.real` and `Rat.AbsoluteValue.padic p`, and `Rat.AbsoluteValue.not_real_isEquiv_padic` is the first computation of the example.

<?decl Rat.AbsoluteValue.equiv_real_or_padic?>
<?decl Rat.AbsoluteValue.not_real_isEquiv_padic?>
:::

**Example (Powers of an absolute value).** For $0 < c \le 1$, the map $x \mapsto |x|_\infty^c$ is an absolute value on $\mathbb{Q}$, since $(s + t)^c \le s^c + t^c$ for $s, t \ge 0$. It is equivalent to $|\cdot|_\infty$ and gives the same topology. For a $p$-adic absolute value, every power $|\cdot|_p^c$ with $c > 0$ is an absolute value, because $|x + y|_p \le \max(|x|_p, |y|_p)$ and this inequality survives the power.

**Example (A counterexample: a power that is not an absolute value).** The map $x \mapsto |x|_\infty^2$ on $\mathbb{Q}$ is multiplicative and orders $\mathbb{Q}$ as $|\cdot|_\infty$ does, but it is not an absolute value: $|1 + 1|^2 = 4 > 2 = |1|^2 + |1|^2$. So not every power of an absolute value is an absolute value, and the theorem on powers starts from two absolute values. The trivial absolute value is a second boundary case: it is equivalent only to itself (`AbsoluteValue.isEquiv_trivial_iff_eq_trivial`), and weak approximation fails for it, since the diagonal of a discrete space $F \times F$ is not dense.

**Remark (Common errors).** In Mathlib, `IsEquiv` is the order condition and not the condition on topologies. To pass to topologies, use `isEquiv_iff_isHomeomorph`, which is stated for absolute values with values in `ℝ` on a field. A second error is to forget that `WithAbs v` and `WithAbs w` are different types with the same elements: a statement about the topology of `v` must be made on `WithAbs v`, since `F` itself may carry another topology from an instance.

### The library around it

The module `Mathlib.Analysis.AbsoluteValue.Equivalence` holds all the results of this section. It uses `Mathlib.Analysis.Normed.Ring.WithAbs` for the normed field `WithAbs v` and its completion. The theorem of Ostrowski for $\mathbb{Q}$ is in `Mathlib.NumberTheory.Ostrowski`. Absolute values with the stronger inequality $v(x + y) \le \max(v(x), v(y))$ are nonarchimedean; the next section treats the topology of such absolute values in the more general language of valuations.

### Exercises

1. (A) Show that `IsEquiv` is an equivalence relation on the absolute values of $F$.
2. (A) Show that if $v$ and $w$ are equivalent and $v$ is nontrivial, then $w$ is nontrivial.
3. (A) Show that $|\cdot|_2$ and $|\cdot|_2^{1/3}$ are equivalent absolute values on $\mathbb{Q}$, and find the constant $c$ of the theorem on powers.
4. (B) Let $v$ be an absolute value on $F$. Show that $v^c$ is an absolute value for every $0 < c \le 1$.
5. (B) Find $y \in \mathbb{Q}$ with $|y - 1|_2 < 1/4$ and $|y|_3 < 1/9$. *Hint:* use the Chinese remainder theorem.
6. (B) Show that the trivial absolute value on $F$ is not equivalent to a nontrivial one, with the definition of `IsEquiv`.
7. (C) Let $v$ and $w$ be equivalent absolute values on $F$. Show that the diagonal $\{(x, x) : x \in F\}$ is closed in $F_v \times F_w$, so that weak approximation fails for two equivalent absolute values. *Hint:* the diagonal is the graph of the identity map, which is continuous by the theorem on topology, and $F_w$ is Hausdorff.

### Notes and history

Ostrowski classified the absolute values of $\mathbb{Q}$ in 1916. The weak approximation theorem is due to Artin and Whaples (1945), as part of their axiomatic treatment of class field theory. The Mathlib module states equivalence by the order condition and proves the topological and the power forms as theorems, which lets the definition work for absolute values with values in any ordered semiring.

### Reference

<?reference?>
