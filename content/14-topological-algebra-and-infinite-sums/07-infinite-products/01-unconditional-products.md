---
title: "Unconditional products: HasProd, Multipliable and tprod"
kind: theory
modules:
  - Mathlib.Topology.Algebra.Indicator
explains:
  E3: [HasProd, Multipliable, tprod, hasProd_zero_of_exists_eq_zero, tprod_one_add]
  E2: [HasProd.unique, HasProd.tprod_eq, Multipliable.hasProd, tprod_eq_one_of_not_multipliable, hasProd_fintype, hasProd_one, HasProd.mul, Multipliable.mul, Multipliable.tprod_mul, HasProd.inv, HasProd.div, Multipliable.tendsto_cofinite_one, multipliable_iff_cauchySeq_finset, HasProd.tendsto_prod_nat, hasProd_nat_add_iff, HasProd.of_nat_of_neg_add_one, Multipliable.tprod_mul_tprod_compl, multipliable_one_add_of_summable_prod, hasProd_one_add_of_hasSum_prod, ENNReal.multipliable_of_le_one, ENNReal.tprod_eq_iInf_prod, ENNReal.hasProd_iInf_prod]
  E1: auto
families: []
requires: [V06, V13, V14.C04, V14.C05, V14.C06]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Unconditional products: HasProd, Multipliable and tprod

### Overview

This section defines the unconditional product of a family in a commutative topological monoid and proves its first properties. Most of them are the rules of Chapter 4 written with multiplication. The new points are three. A product with a factor $0$ is $0$, against the classical convention. A product $\prod (1 + f_i)$ expands into the sum of the products $\prod_{i \in s} f_i$. In $[0, 1] \subseteq [0, \infty]$ every product exists.

### Definitions

Let $M$ be a commutative monoid with a topology and $f : I \to M$. For a finite $F \subseteq I$ write $P_F = \prod_{i \in F} f_i$. The family *has the product* $a$ when $P_F \to a$ along the filter $\mathrm{atTop}$ of the finite subsets of $I$. It is *multipliable* when it has a product. The *product* $\prod' f$ is a chosen product when $f$ is multipliable and $1$ otherwise. As for sums, the definition takes an optional summation filter, with the unconditional filter as default.

::: mathlib
`HasProd` · `Mathlib.Topology.Algebra.InfiniteSum.Defs`

The definition `HasProd f a L`, with `L : SummationFilter β` optional. The attribute `to_additive` generates `HasSum` from it, so each lemma on `HasProd` has an additive twin with the same proof. The predicate `Multipliable` and the function `tprod` follow the same pattern, with the notation `∏' i, f i`.

<?decl HasProd?>
<?decl Multipliable?>
<?decl tprod?>
:::

The junk value is $1$, the unit of the monoid: `tprod_eq_one_of_not_multipliable`. The basic facts transfer from Chapter 4 with the same proofs. The product is unique in a Hausdorff space (`HasProd.unique`), a finite family has its finite product (`hasProd_fintype`), the constant family $1$ has the product $1$ (`hasProd_one`), and the product of two multipliable families is multipliable when multiplication is continuous, with $\prod' f g = \prod' f \cdot \prod' g$ (`HasProd.mul`, `Multipliable.tprod_mul`). In a commutative topological group the inverse and the quotient of products behave in the same way (`HasProd.inv`, `HasProd.div`), and the Cauchy criterion holds in a complete group (`multipliable_iff_cauchySeq_finset`). For $I = \mathbb{N}$ the partial products tend to the product (`HasProd.tendsto_prod_nat`).

### Theorems and proofs

**Theorem (A factor zero).** Let $M$ be a commutative monoid with zero and a topology, and $f : I \to M$ with $f_b = 0$ for some $b$. Then $f$ has the product $0$.

*Proof.* For each finite $F \ni b$, $P_F = 0$, since the factor $f_b$ appears. The sets $F \ni b$ form a set of the filter $\mathrm{atTop}$. So $P_F$ is eventually equal to $0$, and it tends to $0$. $\square$

::: mathlib
`hasProd_zero_of_exists_eq_zero` · `Mathlib.Topology.Algebra.InfiniteSum.Basic`

The statement takes `∃ b, f b = 0` and concludes `HasProd f 0 L` for any summation filter with `L.LeAtTop`. No hypothesis on the topology is needed.

<?decl hasProd_zero_of_exists_eq_zero?>
:::

**Theorem (Terms tend to one in a group).** Let $G$ be a commutative topological group and $f : I \to G$ multipliable. Then $f_i \to 1$ along the cofinite filter.

*Proof.* This is the multiplicative form of the theorem of Chapter 4 on sums. Let $a$ be the product and $U$ a neighbourhood of $1$. Choose a neighbourhood $V$ of $1$ with $V^{-1} V \subseteq U$. There is a finite $F_0$ with $P_F \in a V$ for all $F \supseteq F_0$. For $i \notin F_0$, $f_i = P_{F_0}^{-1} P_{F_0 \cup \{i\}} \in V^{-1} a^{-1} a V = V^{-1} V \subseteq U$. So $f_i \in U$ for all $i$ outside the finite set $F_0$. $\square$

The theorem needs inverses. In the monoid $(\mathbb{R}, \cdot)$ it fails: the family $(0, 5, 5, 5, \dots)$ has the product $0$, by the previous theorem, and its terms tend to $5$.

**Theorem (Expansion of a product).** Let $R$ be a commutative topological semiring and $f : I \to R$. Suppose that the family $s \mapsto \prod_{i \in s} f_i$, indexed by the finite subsets $s$ of $I$, has the sum $a$. Then $i \mapsto 1 + f_i$ has the product $a$. If $R$ is Hausdorff, then $\prod' (1 + f_i) = \sum'_s \prod_{i \in s} f_i$.

*Proof.* For a finite $F$, expanding the product gives
$$\prod_{i \in F} (1 + f_i) = \sum_{s \subseteq F} \prod_{i \in s} f_i ,$$
which is the finite sum of the family $g(s) = \prod_{i \in s} f_i$ over the finite set $\mathcal{P}(F)$ of subsets of $F$. The map $F \mapsto \mathcal{P}(F)$ tends to $\mathrm{atTop}$ on the finite sets of finite subsets of $I$: given a finite collection $\mathcal{C}$ of finite sets, let $F_0$ be their union; then $\mathcal{P}(F) \supseteq \mathcal{C}$ for every $F \supseteq F_0$. The finite sums of $g$ tend to $a$ along $\mathrm{atTop}$, so their composition with $F \mapsto \mathcal{P}(F)$ tends to $a$. This composition is $F \mapsto \prod_{i \in F} (1 + f_i)$. The formula for `tprod` follows by uniqueness. $\square$

::: mathlib
`tprod_one_add` · `Mathlib.Topology.Algebra.InfiniteSum.Ring`

The statement takes `Summable fun s : Finset ι ↦ ∏ i ∈ s, f i` and concludes `∏' i, (1 + f i) = ∑' s : Finset ι, ∏ i ∈ s, f i`, with `T2Space α`. The forms with `HasSum` and `Multipliable` are `hasProd_one_add_of_hasSum_prod` and `multipliable_one_add_of_summable_prod`.

<?decl tprod_one_add?>
:::

**Corollary (Products of 1 + nonnegative terms).** Let $f : I \to \mathbb{R}$ be nonnegative and summable. Then $i \mapsto 1 + f_i$ is multipliable, and $1 \le \prod' (1 + f_i) \le \exp(\sum' f)$.

*Proof.* Let $\mathcal{C}$ be a finite collection of finite subsets of $I$ and $F$ their union. The terms $\prod_{i \in s} f_i$ are nonnegative, so
$$\sum_{s \in \mathcal{C}} \prod_{i \in s} f_i \le \sum_{s \subseteq F} \prod_{i \in s} f_i = \prod_{i \in F} (1 + f_i) \le \prod_{i \in F} e^{f_i} = e^{S_F} \le e^{\sum' f},$$
by the inequality $1 + x \le e^x$ and by Section 5.1. So the family $s \mapsto \prod_{i \in s} f_i$ has bounded finite sums and is summable by Section 5.1. The theorem gives the product, and the same bound holds for its value, the supremum of the finite sums. The term $s = \emptyset$ contributes $1$, which gives the lower bound. $\square$

::: mathlib
`Real.add_one_le_exp` · `Mathlib.Analysis.Complex.Exponential`

The inequality `x + 1 ≤ Real.exp x` for every real `x`. Section 2 removes the hypothesis $f \ge 0$ with the logarithm.

<?decl Real.add_one_le_exp?>
:::

**Theorem (Products in [0, 1]).** Let $f : I \to [0, \infty]$ with $f_i \le 1$ for every $i$. Then $f$ has the product $\inf_F P_F$.

*Proof.* Since the factors are at most $1$, the finite products decrease when $F$ grows: $P_{F'} = P_F \cdot P_{F' \setminus F} \le P_F$ for $F \subseteq F'$. The infimum $b = \inf_F P_F$ exists in the complete lattice $[0, \infty]$. In the order topology an antitone net converges to its infimum: for $c > b$ some $P_{F_0} < c$, and then $b \le P_F \le P_{F_0} < c$ for all $F \supseteq F_0$. So $P_F \to b$. $\square$

::: mathlib
`ENNReal.tprod_eq_iInf_prod` · `Mathlib.Topology.Algebra.InfiniteSum.ENNReal`

The statement `∏' i, f i = ⨅ s, ∏ i ∈ s, f i` under `∀ i, f i ≤ 1`. The forms with `HasProd` and `Multipliable` are `ENNReal.hasProd_iInf_prod` and `ENNReal.multipliable_of_le_one`. In probability these products give the probability that infinitely many independent events all fail.

<?decl ENNReal.tprod_eq_iInf_prod?>
:::

### Examples

**Example (A product that diverges to zero).** Let $f(n) = 1 - 1/n$ for $n \ge 2$, as a family on $\{n \ge 2\}$. The partial products telescope: $\prod_{n=2}^{N} \frac{n-1}{n} = \frac{1}{N}$. Every factor lies in $[0, 1]$, so for a finite $F \supseteq \{2, \dots, N\}$, $0 \le P_F \le 1/N$. Hence $P_F \to 0$, and the family has the product $0$ in Mathlib. The classical theory says that this product diverges to $0$.

**Example (Binary expansion).** Let $0 \le x < 1$ and $f(n) = x^{2^n}$ on $\mathbb{N}$. For a finite $s \subseteq \mathbb{N}$, $\prod_{n \in s} x^{2^n} = x^{m(s)}$ with $m(s) = \sum_{n \in s} 2^n$. The map $s \mapsto m(s)$ is a bijection from the finite subsets of $\mathbb{N}$ onto $\mathbb{N}$, by binary expansion. So the family $s \mapsto x^{m(s)}$ is a reindexing of the geometric family $m \mapsto x^m$, which has the sum $1/(1-x)$. The theorem on expansion gives
$$\prod_{n \ge 0} \bigl(1 + x^{2^n}\bigr) = \frac{1}{1 - x}.$$

**Example (A counterexample: an oscillating product).** Let $f(n) = -1$ for all $n \in \mathbb{N}$. The finite product $P_F = (-1)^{|F|}$ takes both values $\pm 1$ on arbitrarily large sets, so it has no limit, and $f$ is not multipliable in $\mathbb{R}$. Its `tprod` is the junk value $1$. The same happens for $f(n) = 2$, whose finite products tend to $+\infty$.

**Remark (Common errors).** In Mathlib, `Multipliable f` does not mean that the product converges in the classical sense. A family with one factor $0$ is multipliable, and so is a family whose finite products tend to $0$. Results that need a nonzero product, such as the relation with logarithms in Section 2, state the condition explicitly. A second error is to forget the junk value: $\prod' f = 1$ does not imply that $f$ is multipliable.

### The library around it

The product lemmas sit in the same modules as the sum lemmas of Chapter 4, `Mathlib.Topology.Algebra.InfiniteSum.Defs`, `Basic`, `Group`, `NatInt` and `Constructions`, because each sum lemma is generated from a product lemma. The names follow the dictionary of `to_additive`: `mul` for `add`, `inv` for `neg`, `div` for `sub` and `one` for `zero`. The expansion of $\prod (1 + f_i)$ and its ordered variants such as `tprod_one_add_ordered` are in `Mathlib.Topology.Algebra.InfiniteSum.Ring`. The module `Mathlib.Topology.Algebra.Indicator` proves the continuity of `Set.mulIndicator`, the function equal to $f$ on a set and to $1$ outside, whose additive twin `Set.indicator` restricts a sum to a subset.

### Exercises

1. (A) Show that the family $f(n) = 1$ for $n \ne 3$, $f(3) = 7$, has the product $7$.
2. (A) Let $f, g : I \to \mathbb{R}$ be multipliable. Show that $\prod' f g = \prod' f \cdot \prod' g$.
3. (A) Compute $\prod_{n \ge 2} \bigl(1 - \frac{1}{n^2}\bigr)$ from the partial products. *Hint:* the factor is $\frac{(n-1)(n+1)}{n \cdot n}$, and the answer is $1/2$.
4. (B) Show that $\prod_{n \ge 1} (1 + 1/n)$ is not multipliable in $\mathbb{R}$.
5. (B) Let $(p_i)$ be numbers in $[0, 1]$. Show that $\prod' (1 - p_i) = 0$ in `ℝ≥0∞` when $\sum p_i = \infty$. *Hint:* $1 - p \le e^{-p}$.
6. (B) Give a commutative topological monoid $M$ and a multipliable family whose terms do not tend to $1$ along the cofinite filter, other than the example of the section.
7. (C) Let $0 \le x < 1$. Compute $\prod_{n \ge 0} (1 + x^{3^n} + x^{2 \cdot 3^n})$. *Hint:* expansion in base $3$.

### Notes and history

Infinite products appear in the work of Wallis and of Euler, who found the product formula for the sine and the product of the zeta function over the primes. Mathlib chose the uniform definition of a limit of finite products and treats the nonvanishing as a separate statement.

### Reference

<?reference?>
