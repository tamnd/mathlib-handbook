---
title: Cofinality
kind: theory
modules:
  - Mathlib.SetTheory.Cardinal.Cofinality.Basic
  - Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
  - Mathlib.SetTheory.Cardinal.Cofinality.Enum
explains:
  E3: [Order.cof, Ordinal.cof, Ordinal.exists_ord_cof_eq, Cardinal.lt_power_cof_ord, Order.enum]
  E2: [Order.cof_le, Order.le_cof_iff, Order.cof_le_cardinalMk, Order.cof_eq_one_iff, Order.cof_lt_aleph0_iff, Order.cof_congr_of_strictMono, Order.cof_nat, Ordinal.cof_le_card, Ordinal.cof_add_one, Ordinal.one_lt_cof_iff, Ordinal.cof_omega0, Ordinal.cof_ord_cof, Ordinal.cof_add, Ordinal.cof_map_of_isNormal, Ordinal.iSup_lt_of_lt_cof, Ordinal.cof_omega, Cardinal.lt_cof_ord_power, Order.type_eq_of_isCofinal, IsRegularCardinalOrder]
  E1: auto
families: []
requires: [V31.C01, V31.C02, V31.C04, V31.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Cofinality

### Overview

A subset of an order is cofinal if each element of the order lies below some element of the subset. The cofinality of the order is the least cardinality of a cofinal subset. It measures how many steps are necessary to climb to the top of the order. The natural numbers need $\aleph_0$ steps. An order with a largest element needs one step. The ordinal $\omega_\omega$ has cardinality $\aleph_\omega$, but $\aleph_0$ steps are sufficient.

Mathlib defines the cofinality for each preorder, and defines the cofinality of an ordinal as the cofinality of a well-order of that type. This section proves the basic facts: the cofinality of a well-order is attained by a cofinal subset of the least possible order type, it is idempotent, and the normal functions of Chapter 4 keep it unchanged at limits. The last theorem combines the cofinality with the theorem of König from Chapter 1. It gives $\kappa < \kappa^{\operatorname{cf} \kappa}$, and so $2^{\aleph_0} \ne \aleph_\omega$.

### Definitions

**Definition (Cofinal subset).** Let $(P, \le)$ be a preorder. A subset $S \subseteq P$ is *cofinal* if for each $a \in P$ there is $b \in S$ with $a \le b$.

**Definition (Cofinality of an order).** The *cofinality* $\operatorname{cf} P$ of a preorder $P$ is the least cardinal $|S|$ for $S$ a cofinal subset of $P$.

The set $P$ itself is cofinal, so $\operatorname{cf} P \le |P|$. The least cardinal exists because the cardinals are well-ordered. Thus there is always a cofinal subset of cardinality exactly $\operatorname{cf} P$.

**Definition (Cofinality of an ordinal).** For an ordinal $o$, $\operatorname{cf} o$ is the cofinality of a well-order of type $o$, for example the set of ordinals below $o$.

Two well-orders of the same type are isomorphic, and an isomorphism carries cofinal subsets to cofinal subsets of the same size. So the definition does not depend on the choice of the well-order.

For a cardinal $\kappa$, the cofinality of $\kappa$ is the cofinality of its initial ordinal $\kappa.\mathrm{ord}$ from Chapter 5. Mathlib has no separate function for it and writes `c.ord.cof`.

**Definition (Regular cardinal order).** A well-order $W$ is a *regular cardinal order* if its order type is at most the initial ordinal of $\operatorname{cf} W$.

The orders $\mathbb{N}$ and the class of all ordinals of a universe are examples. Section 2 shows that the infinite examples are exactly the orders of type $\kappa.\mathrm{ord}$ for $\kappa$ a regular cardinal. The name comes from that fact.

### Theorems and proofs

**Proposition (Small cofinalities).** Let $L$ be a linear order.

1. $\operatorname{cf} L = 0$ if and only if $L$ is empty.
2. $\operatorname{cf} L = 1$ if and only if $L$ has a largest element.
3. $\operatorname{cf} L < \aleph_0$ if and only if $\operatorname{cf} L \le 1$.

*Proof.* (1) The empty set is cofinal exactly when there is no element to dominate. (2) If $t$ is the largest element, $\{t\}$ is cofinal. Conversely, if $\{t\}$ is cofinal, then each $a$ satisfies $a \le t$. (3) Let $S$ be a finite cofinal subset. If $S$ is empty, $L$ is empty. Otherwise $S$ has a largest element $t$, because $L$ is linear, and each $a \in L$ lies below some element of $S$, hence below $t$. So $\{t\}$ is cofinal and $\operatorname{cf} L \le 1$. $\square$

So a linear order has cofinality 0, 1, or an infinite cardinal. The values 2, 3, ... do not occur.

**Lemma (Invariance).** Let $f : A \to B$ be a strictly increasing map between linear orders, with cofinal range. Then $\operatorname{cf} A = \operatorname{cf} B$.

*Proof.* Let $S$ be cofinal in $A$. For $b \in B$, take $a$ with $b \le f(a)$, then $s \in S$ with $a \le s$. So $b \le f(s)$, and $f(S)$ is cofinal in $B$. Thus $\operatorname{cf} B \le |S|$, and $\operatorname{cf} B \le \operatorname{cf} A$.

Conversely, let $T$ be cofinal in $B$. For each $t \in T$, choose $a_t \in A$ with $t \le f(a_t)$. Let $a \in A$. Take $t \in T$ with $f(a) \le t$. Then $f(a) \le f(a_t)$. A strictly increasing map between linear orders reflects the order, so $a \le a_t$. Thus $\{a_t\}$ is cofinal in $A$, of size at most $|T|$. $\square$

As a special case, a cofinal subset $S$ of a linear order $L$ has $\operatorname{cf} S = \operatorname{cf} L$.

**Theorem (Cofinal subsets of least type).** Let $W$ be a well-order. There is a cofinal subset $T \subseteq W$ of order type $(\operatorname{cf} W).\mathrm{ord}$.

*Proof.* Let $\kappa = \operatorname{cf} W$, and let $S$ be a cofinal subset with $|S| = \kappa$. Put on $S$ a second well-order $\prec$ of type $\kappa.\mathrm{ord}$. Let $T$ be the set of $x \in S$ that are larger in $W$ than each $\prec$-predecessor of $x$.

$T$ is cofinal. Let $a \in W$. The set of $y \in S$ with $a \le y$ is not empty, so it has a $\prec$-least element $x$. If $y \prec x$, then $y < a \le x$ by the choice of $x$. So $x \in T$, and $a \le x$.

On $T$, the two orders agree. If $x, y \in T$ and $y \prec x$, then $y < x$ by the definition of $T$. Two linear orders on the same set in which one relation implies the other are equal. So $(T, <)$ is a subset of $(S, \prec)$ with the induced order, and its type is at most $\kappa.\mathrm{ord}$. Also $|T| \ge \kappa$ because $T$ is cofinal, so the type of $T$ is at least $\kappa.\mathrm{ord}$. $\square$

**Corollary (Idempotence).** $\operatorname{cf}((\operatorname{cf} o).\mathrm{ord}) = \operatorname{cf} o$ for each ordinal $o$. Also $\operatorname{cf} o \le |o|$, and $(\operatorname{cf} o).\mathrm{ord} \le o$.

*Proof.* Take $T$ as in the theorem, for a well-order of type $o$. By the lemma, $\operatorname{cf} T = \operatorname{cf} o$, and $T$ has type $(\operatorname{cf} o).\mathrm{ord}$. The second claim is $\operatorname{cf} \le |\cdot|$. For the third, $T$ is a subset of the well-order, so its type is at most $o$. $\square$

**Theorem (Cofinality of ordinals).**

1. $\operatorname{cf} 0 = 0$ and $\operatorname{cf}(o + 1) = 1$.
2. If $o$ is a limit ordinal, then $\operatorname{cf} o \ge \aleph_0$. In particular $\operatorname{cf} \omega = \aleph_0$.
3. If $f$ is a normal function and $a$ is a limit ordinal, then $\operatorname{cf} f(a) = \operatorname{cf} a$.
4. If $b \ne 0$, then $\operatorname{cf}(a + b) = \operatorname{cf} b$.

*Proof.* (1) The ordinal $o + 1$ has the largest element $o$. (2) A limit ordinal has no largest element, so its cofinality is not 0 or 1, hence infinite by the proposition. Also $\operatorname{cf} \omega \le |\omega| = \aleph_0$. (3) By the definition of a normal function, $f(a) = \sup_{b < a} f(b)$, and $f$ is strictly increasing. So $f$ maps $[0, a)$ into $[0, f(a))$ with cofinal range, and the lemma gives the claim. (4) If $b = c + 1$, both sides are 1. If $b$ is a limit, apply (3) to the normal function $x \mapsto a + x$. $\square$

**Theorem (Small suprema).** Let $a$ be an ordinal and let $(f_i)_{i \in I}$ be ordinals below $a$, with $|I| < \operatorname{cf} a$. Then $\sup_i f_i < a$.

*Proof.* If $\sup_i f_i \ge a$, then each $b < a$ is below some $f_i$, because $b$ is not an upper bound. So $\{f_i\}$ is cofinal in $[0, a)$, and $\operatorname{cf} a \le |I|$. $\square$

**Theorem (König).** Let $\kappa$ be an infinite cardinal. Then $\kappa < \kappa^{\operatorname{cf} \kappa}$.

*Proof.* Let $W$ be a well-order of type $\kappa.\mathrm{ord}$ and let $S \subseteq W$ be cofinal with $|S| = \operatorname{cf} \kappa$. As $\kappa$ is infinite, $\kappa.\mathrm{ord}$ is a limit ordinal, so $W$ has no largest element. Thus $W = \bigcup_{x \in S} \{y : y < x\}$. Each set $\{y : y < x\}$ has an order type below the initial ordinal $\kappa.\mathrm{ord}$, so its cardinality is less than $\kappa$. The theorem of König from Chapter 1 gives $$\kappa \le \sum_{x \in S} |\{y : y < x\}| < \prod_{x \in S} \kappa = \kappa^{\operatorname{cf} \kappa}.$$ $\square$

**Corollary (Cofinality of powers).** Let $a$ be infinite and $b > 1$. Then $a < \operatorname{cf}(b^a)$. In particular, $\operatorname{cf}(2^{\aleph_0}) > \aleph_0$.

*Proof.* Put $\mu = b^a$, which is infinite. If $\operatorname{cf} \mu \le a$, then $\mu^{\operatorname{cf} \mu} \le \mu^a = b^{a \cdot a} = b^a = \mu$ by the theorem $a \cdot a = a$ of Chapter 5. This contradicts König. $\square$

### Examples

**Example (Computations).** By the theorem on ordinals, $\operatorname{cf}(\omega \cdot 2 + 7) = 1$ and $\operatorname{cf}(\omega_1 + \omega) = \operatorname{cf} \omega = \aleph_0$. The map $x \mapsto \omega \cdot x$ is normal, so $\operatorname{cf}(\omega^2) = \operatorname{cf}(\omega \cdot \omega) = \aleph_0$. The map $\alpha \mapsto \omega_\alpha$ is normal, so $\operatorname{cf}(\omega_\omega) = \aleph_0$ while $|\omega_\omega| = \aleph_\omega$. The cofinality of $\omega_{\omega_1}$ is $\operatorname{cf}(\omega_1)$, which Section 2 shows to be $\aleph_1$. Outside the well-orders, $\mathbb{Z}$, $\mathbb{Q}$ and $\mathbb{R}$ all have cofinality $\aleph_0$, because $\mathbb{N}$ is cofinal in each of them and none has a largest element.

**Example (The continuum is not $\aleph_\omega$).** The cofinality of $\aleph_\omega$ is $\aleph_0$ by the first example. The corollary on powers gives $\operatorname{cf}(2^{\aleph_0}) > \aleph_0$. So $2^{\aleph_0} \ne \aleph_\omega$. The same argument excludes $\aleph_{\omega + \omega}$, $\aleph_{\omega^2}$ and $\aleph_{\omega_\omega}$. Chapter 5 records that the index of this edition has no declaration for the independence of the continuum hypothesis, and this restriction is one of the few that ZFC proves.

**Counterexample (Limits are necessary).** In part 3 of the theorem on ordinals, the hypothesis that $a$ is a limit is necessary. The map $\alpha \mapsto \omega_\alpha$ is normal, and $\operatorname{cf} 1 = 1$, but $\operatorname{cf}(\omega_1) \ne 1$ because $\omega_1$ is a limit ordinal. In part 4, $b \ne 0$ is necessary: $\operatorname{cf}(\omega + 0) = \aleph_0$ but $\operatorname{cf} 0 = 0$.

**Counterexample (Linearity is necessary).** In a preorder that is not linear, the proposition fails. Let $P$ be a set of 2 incomparable elements. The only cofinal subset is $P$ itself, so $\operatorname{cf} P = 2$.

### The library around it

::: mathlib
`Order.cof` · `Mathlib.SetTheory.Cardinal.Cofinality.Basic`

`Order.cof α` is defined for each `[Preorder α]` as `⨅ s : {s : Set α // IsCofinal s}, #s`. The basic lemmas are `Order.cof_le (h : IsCofinal s) : cof α ≤ #s`, `Order.le_cof_iff`, `Order.cof_le_cardinalMk`, `Order.cof_eq_one_iff : cof α = 1 ↔ ∃ x, IsTop x` and, for linear orders, `Order.cof_lt_aleph0_iff`. The lemma of invariance is `Order.cof_congr_of_strictMono`. Concrete values: `Order.cof_nat : cof ℕ = ℵ₀` and `Order.cof_int`.

<?decl Order.cof?>
:::

::: mathlib
`Ordinal.cof` · `Mathlib.SetTheory.Cardinal.Cofinality.Ordinal`

`Ordinal.cof o` is the cofinality of a well-order of type `o`, and `Ordinal.cof_type` connects it to `Order.cof`. The lemmas of the theorem on ordinals are `Ordinal.cof_le_card`, `Ordinal.cof_add_one`, `Ordinal.one_lt_cof_iff : 1 < cof o ↔ IsSuccLimit o`, `Ordinal.cof_omega0`, `Ordinal.cof_map_of_isNormal`, `Ordinal.cof_add` and `Ordinal.cof_omega`. Small suprema are `Ordinal.iSup_lt_of_lt_cof`.

<?decl Ordinal.cof?>
:::

::: mathlib
`Ordinal.exists_ord_cof_eq` · `Mathlib.SetTheory.Cardinal.Cofinality.Ordinal`

`exists_ord_cof_eq α : ∃ s : Set α, IsCofinal s ∧ typeLT s = (Order.cof α).ord` for a well-order `α`. Idempotence is `Ordinal.cof_ord_cof : o.cof.ord.cof = o.cof`.

<?decl Ordinal.exists_ord_cof_eq?>
:::

::: mathlib
`Cardinal.lt_power_cof_ord` · `Mathlib.SetTheory.Cardinal.Cofinality.Ordinal`

`lt_power_cof_ord (hc : ℵ₀ ≤ c) : c < c ^ c.ord.cof`. The proof in Mathlib is the proof above, with `Cardinal.sum_lt_prod`. The corollary is `Cardinal.lt_cof_ord_power (ha : ℵ₀ ≤ a) (hb : 1 < b) : a < (b ^ a).ord.cof`.

<?decl Cardinal.lt_power_cof_ord?>
:::

<?decl Cardinal.lt_cof_ord_power?>

::: mathlib
`Order.enum` · `Mathlib.SetTheory.Cardinal.Cofinality.Enum`

For a well-order `α` with `[IsRegularCardinalOrder α]` and a cofinal set `s`, `Order.enum s hs : α ≃o s` is the unique isomorphism of `α` with `s`. It exists because of `Order.type_eq_of_isCofinal`: each cofinal subset has the type of `α`. For `α = Ordinal` it enumerates an unbounded class of ordinals, as `Ordinal.enumOrd` of Chapter 4 does.

<?decl Order.enum?>
:::

<?decl IsRegularCardinalOrder?>

Common errors:

- There is no function `Cardinal.cof`. The cofinality of a cardinal `c` is `c.ord.cof`, and the hypotheses of many lemmas have this form.
- `Order.cof` exists for each preorder, so `Order.cof ℝ` is meaningful and equals $\aleph_0$. The value of `Ordinal.cof o` is `Order.cof` of `o.ToType`, by `Ordinal.cof_toType`.
- The lemma `Ordinal.cof_succ` and the alias `Ordinal.ord_cof_eq` are deprecated. Use `Ordinal.cof_add_one` and `Ordinal.exists_ord_cof_eq`.
- The cofinality of a set of ordinals in `Ordinal.{u}` lives one universe higher. `Ordinal.cof_Iio` carries a `lift` for this reason.
- A cofinality of 1 does not mean a small ordinal. $\operatorname{cf}(\omega_5 + 1) = 1$.

### Exercises

1. (A) Compute $\operatorname{cf}(\omega^\omega)$, $\operatorname{cf}(\omega_2 \cdot 3)$, $\operatorname{cf}(\omega_2 \cdot \omega)$ and $\operatorname{cf}(\omega_{\omega + 1} + \omega_3)$.
2. (A) Show that the cofinality of a finite nonempty linear order is 1, and that the cofinality of $\mathbb{R}$ is $\aleph_0$.
3. (B) Show that $\operatorname{cf}(\operatorname{cf} o) $ makes sense only after the passage through $\mathrm{ord}$, and prove directly that $\operatorname{cf}(\omega_\omega) = \aleph_0$ from the definition.
4. (B) Show that $\operatorname{cf} o$ is the least ordinal $\beta$, read as a cardinal, such that there is a strictly increasing map $\beta \to o$ with cofinal range. Hint: use the theorem on cofinal subsets of least type.
5. (B) Let $f$ be a normal function. Show that $\operatorname{cf} a \le \operatorname{cf} f(a)$ for each ordinal $a$. Hint: treat the successor case separately.
6. (B) Show that $\aleph_\omega^{\aleph_0} > \aleph_\omega$. Then show that $2^{\aleph_1} \ne \aleph_{\omega_1}$.
7. (C) Let $P$ be a directed preorder. Show that $\operatorname{cf} P$ need not be the cofinality of any linear order, by computing $\operatorname{cf}(\mathbb{N} \times \mathbb{N})$ and $\operatorname{cf}$ of the finite subsets of $\omega_1$ under inclusion.

### Notes and history

Hausdorff introduced the cofinality in his studies of ordered sets in the first decade of the twentieth century, and he raised the question of regular limit cardinals. König proved his inequality in 1905, and the consequence $\operatorname{cf}(2^{\aleph_0}) > \aleph_0$ is the main restriction on the continuum that ZFC gives. Easton showed in 1970 that for regular cardinals the restrictions of monotonicity and of König are the only ones.

### Reference

<?reference?>
