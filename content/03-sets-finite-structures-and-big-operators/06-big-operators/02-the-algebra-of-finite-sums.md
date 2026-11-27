---
title: The algebra of finite sums
kind: theory
modules:
  - Mathlib.Algebra.BigOperators.Group.Finset.Sigma
  - Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
  - Mathlib.Algebra.BigOperators.Intervals
  - Mathlib.Algebra.Order.BigOperators.Group.Finset
  - Mathlib.Algebra.Order.BigOperators.Ring.Finset
explains:
  E3: [Finset.sum_bij, Finset.sum_comm, Finset.sum_mul_sq_le_sq_mul_sq]
  E2: [Finset.sum_nbij', Finset.sum_equiv, Finset.sum_image, Finset.sum_range_reflect, Finset.sum_union, Finset.sum_filter_add_sum_filter_not, Finset.sum_range_add, Finset.sum_product, Finset.sum_sigma, Finset.sum_comm', Finset.sum_range_sub, Finset.sum_le_sum, Finset.sum_nonneg, Finset.abs_sum_le_sum_abs, Finset.sum_ite, Finset.sum_boole]
  E1: auto
families: []
requires: [V03.C03, V03.C04]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V03/C06/Examples.lean
  - MathlibHandbook/V03/C06/Exercises.lean
  - MathlibHandbook/V03/C06/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The algebra of finite sums

### Overview

Section 1 computed sums by induction. Induction needs a closed formula in advance, and it hides the structure of a sum. A working mathematician changes a sum with a few moves. This section states each move as a theorem, proves it, and gives its form in Mathlib.

The moves are these: reindexing by a bijection, splitting over a disjoint union, the exchange of the order of summation (the theorem of Fubini for finite sums), telescoping and the geometric sum, the order rules, the inequality of Cauchy and Schwarz, and the sums of an `if`. Each rule has a twin for products.

### Definitions

**Definition (Reindexing data).** Let $s$ be a finset of $\iota$ and $t$ a finset of $\kappa$. A *bijection from $s$ to $t$* is a map $i : \iota \to \kappa$ with three properties: $i(a) \in t$ for $a \in s$ (it maps $s$ into $t$), $i(a_1) = i(a_2)$ implies $a_1 = a_2$ for $a_1, a_2 \in s$ (it is injective on $s$), and each $b \in t$ is $i(a)$ for some $a \in s$ (it is surjective onto $t$).

The map needs to be a bijection only on $s$. For example, the map $j \mapsto n - 1 - j$ on $\mathbb{N}$ is not injective, because the subtraction of $\mathbb{N}$ truncates, but it is a bijection from `range n` to itself.

**Definition (Product and dependent product of finsets).** For finsets $s$ of $\alpha$ and $t$ of $\beta$, the finset $s \times t$ of $\alpha \times \beta$ has the pairs $(a, b)$ with $a \in s$ and $b \in t$. For a finset $t_a$ of $\beta_a$ for each $a \in s$, the finset $\Sigma_{a \in s} t_a$ has the pairs $\langle a, b\rangle$ with $a \in s$ and $b \in t_a$. The inner finset can depend on $a$, as in a triangle.

**Definition (Sum with a condition).** For a decidable predicate $p$, the sum $\sum_{i \in s,\ p(i)} f(i)$ is the sum over the filter $\{i \in s : p(i)\}$.

::: mathlib
`Finset.sum_product` · `Mathlib.Algebra.BigOperators.Group.Finset.Sigma`

The product finset is `s ×ˢ t`, with the notation `×ˢ` of `SProd`. The dependent form is `s.sigma t` with values in the type `Σ a, σ a`, and its rule is `Finset.sum_sigma`.

<?decl Finset.sum_product?>
:::

### Theorems and proofs

**Theorem (Sum over an image).** Let $g : \kappa \to \iota$ be injective on the finset $s$. Then $\sum_{x \in g(s)} f(x) = \sum_{y \in s} f(g(y))$.

*Proof.* Use induction on $s$. For $s = \emptyset$, the image is empty, and both sums are $0$. Let $a \notin s$, with $g$ injective on $s \cup \{a\}$, and assume the theorem for $s$. The image of $s \cup \{a\}$ is $g(s) \cup \{g(a)\}$. The value $g(a)$ is not in $g(s)$: if $g(a) = g(y)$ with $y \in s$, then $a = y$ by injectivity, and this contradicts $a \notin s$. So the insert rule applies on both sides: $$\sum_{x \in g(s) \cup \{g(a)\}} f(x) = f(g(a)) + \sum_{x \in g(s)} f(x) = f(g(a)) + \sum_{y \in s} f(g(y)) = \sum_{y \in s \cup \{a\}} f(g(y)).$$ $\square$

**Theorem (Reindexing).** Let $i$ be a bijection from $s$ to $t$, and let $f(a) = g(i(a))$ for each $a \in s$. Then $\sum_{a \in s} f(a) = \sum_{b \in t} g(b)$.

*Proof.* The image $i(s)$ is a subset of $t$, because $i$ maps $s$ into $t$. It contains $t$, because $i$ is surjective onto $t$. So $i(s) = t$. The theorem on the sum over an image, with the injectivity of $i$ on $s$, gives $\sum_{b \in t} g(b) = \sum_{a \in s} g(i(a)) = \sum_{a \in s} f(a)$. $\square$

::: mathlib
`Finset.sum_bij` · `Mathlib.Algebra.BigOperators.Group.Finset.Defs`

The map in `Finset.sum_bij` is dependent: `i : ∀ a ∈ s, κ`, so it can use the proof that `a ∈ s`. `Finset.sum_nbij` takes a plain map. `Finset.sum_nbij'` takes `i` and an inverse `j`, and this form is often easier, because the inverse is the witness that surjectivity needs. `Finset.sum_equiv` takes an equivalence `e : ι ≃ κ` with `a ∈ s ↔ e a ∈ t`.

<?decl Finset.sum_bij?>
:::

**Theorem (Reflection).** For each $f : \mathbb{N} \to M$ and $n \in \mathbb{N}$, $$\sum_{j < n} f(n - 1 - j) = \sum_{j < n} f(j).$$

*Proof.* Reindex with $s = t = \mathrm{range}\, n$ and $i(j) = n - 1 - j$. For $j < n$, $n - 1 - j < n$, and the subtraction does not truncate, so $i(i(j)) = j$. So $i$ is its own inverse on $s$, and it is a bijection from $s$ to $s$. $\square$

::: mathlib
`Finset.sum_range_reflect` · `Mathlib.Algebra.BigOperators.Intervals`

The statement is `∑ j ∈ range n, f (n - 1 - j) = ∑ j ∈ range n, f j`, with the truncated subtraction of `ℕ`. The lemma `Finset.prod_range_reflect` is the twin for products.

<?decl Finset.sum_range_reflect?>
:::

**Theorem (Splitting).** If $s_1$ and $s_2$ are disjoint finsets, then $\sum_{s_1 \cup s_2} f = \sum_{s_1} f + \sum_{s_2} f$. For a decidable predicate $p$, $$\sum_{i \in s,\ p(i)} f(i) + \sum_{i \in s,\ \neg p(i)} f(i) = \sum_{i \in s} f(i).$$ For $n, m \in \mathbb{N}$, $\sum_{x < n + m} f(x) = \sum_{x < n} f(x) + \sum_{x < m} f(n + x)$.

*Proof.* For the first rule, use induction on $s_1$. For $a \notin s_1$ with $s_1 \cup \{a\}$ disjoint from $s_2$, $a \notin s_1 \cup s_2$, so the insert rule and the hypothesis give $f(a) + \sum_{s_1} f + \sum_{s_2} f$ on both sides. For the second rule, the two filters are disjoint and their union is $s$. For the third rule, $\mathrm{range}(n + m)$ is the disjoint union of $\mathrm{range}\, n$ and the image of $\mathrm{range}\, m$ under the injective map $x \mapsto n + x$, and the sum over an image gives the second sum. $\square$

The hypothesis of disjointness is needed. For $s_1 = \{0, 1\}$, $s_2 = \{1, 2\}$ and $f = 1$, the left side is $|\{0, 1, 2\}| = 3$, and the right side is $4$.

::: mathlib
`Finset.sum_union` · `Mathlib.Algebra.BigOperators.Group.Finset.Basic`

The hypothesis is `Disjoint s₁ s₂`, in the sense of the lattice of finsets. The lemma `Finset.disjoint_left` turns it into `∀ a, a ∈ s₁ → a ∉ s₂`. The form with an intersection is `Finset.sum_union_inter`.

<?decl Finset.sum_union?>
:::

**Theorem (Fubini for finite sums).** Let $s$ be a finset of $\gamma$, $t$ a finset of $\alpha$ and $f : \gamma \times \alpha \to M$. Then $$\sum_{p \in s \times t} f(p) = \sum_{x \in s} \sum_{y \in t} f(x, y) = \sum_{y \in t} \sum_{x \in s} f(x, y).$$

*Proof.* For each $x \in s$, let $P_x = \{x\} \times t$. The sets $P_x$ are pairwise disjoint, and their union is $s \times t$. Induction on $s$ with the splitting rule gives $\sum_{s \times t} f = \sum_{x \in s} \sum_{p \in P_x} f(p)$. The map $y \mapsto (x, y)$ is injective with image $P_x$, so the sum over an image gives $\sum_{p \in P_x} f(p) = \sum_{y \in t} f(x, y)$. For the second equality, reindex by the swap $(x, y) \mapsto (y, x)$, which is its own inverse, and apply the first equality to $t \times s$. $\square$

The same proof works for a finset $T \subseteq \gamma \times \alpha$ with the slices $T_x = \{y : (x, y) \in T\}$ and $T^y = \{x : (x, y) \in T\}$: $$\sum_{x} \sum_{y \in T_x} f(x, y) = \sum_{(x, y) \in T} f(x, y) = \sum_{y} \sum_{x \in T^y} f(x, y).$$ This exchanges the order of a sum over a triangle.

::: mathlib
`Finset.sum_comm` · `Mathlib.Algebra.BigOperators.Group.Finset.Sigma`

The exchange of two sums over fixed finsets. In a goal with more than two sums, `rw [Finset.sum_comm]` may exchange the wrong pair. Then `Finset.sum_comm'`, which takes a description of the region, or a `conv` selects the pair. The dependent form is `Finset.sum_sigma`.

<?decl Finset.sum_comm?>
:::

**Theorem (Telescoping).** Let $G$ be an additive commutative group and $f : \mathbb{N} \to G$. Then $$\sum_{i < n} \bigl(f(i + 1) - f(i)\bigr) = f(n) - f(0).$$

*Proof.* Use induction on $n$. For $n = 0$, the sum is $0 = f(0) - f(0)$. If the formula holds for $n$, the rule of one more term gives $f(n) - f(0) + f(n + 1) - f(n) = f(n + 1) - f(0)$. $\square$

The group is needed. In $\mathbb{N}$, take $f(0) = 3$, $f(1) = 0$ and $f(2) = 3$. Then $\sum_{i < 2} (f(i + 1) - f(i)) = (0 - 3) + (3 - 0) = 0 + 3 = 3$ with the truncated subtraction, but $f(2) - f(0) = 0$.

::: mathlib
`Finset.sum_range_sub` · `Mathlib.Algebra.BigOperators.Group.Finset.Basic`

The telescope, for an `AddCommGroup`. The twin `Finset.prod_range_div` is the telescope of quotients $\prod f(i + 1)/f(i) = f(n)/f(0)$ in a commutative group. For `ℕ` with a monotone `f`, the form `Finset.sum_range_tsub` holds.

<?decl Finset.sum_range_sub?>
:::

**Theorem (Geometric sums).** Let $R$ be a ring and $x \in R$. Then $\bigl(\sum_{i < n} x^i\bigr)(x - 1) = x^n - 1$. If $R$ is a field and $x \ne 1$, then $$\sum_{i < n} x^i = \frac{x^n - 1}{x - 1}.$$

*Proof.* By the linear rule, $\bigl(\sum_{i < n} x^i\bigr)(x - 1) = \sum_{i < n} (x^{i + 1} - x^i)$. This is a telescope with $f(i) = x^i$, so it is $x^n - x^0 = x^n - 1$. In a field with $x \ne 1$, divide by $x - 1 \ne 0$. $\square$

::: mathlib
`geom_sum_eq` · `Mathlib.Algebra.Field.GeomSum`

The form in a division ring with `x ≠ 1`. The form with no division is `geom_sum_mul`, for any ring. In `ℕ`, `Nat.geomSum_eq` gives the form with the exact division of `ℕ`, for `2 ≤ m`. These files are in Volume 6.

<?decl geom_sum_eq?>
:::

**Theorem (Sums keep the order).** Let $M$ be an ordered additive commutative monoid. If $f(i) \le g(i)$ for each $i \in s$, then $\sum_{i \in s} f(i) \le \sum_{i \in s} g(i)$. If $0 \le f(i)$ for each $i \in s$, then $0 \le \sum_{i \in s} f(i)$. In an ordered additive group, $\bigl|\sum_{i \in s} f(i)\bigr| \le \sum_{i \in s} |f(i)|$.

*Proof.* For the first rule, use induction on $s$. In the step, $f(a) \le g(a)$ and $\sum_s f \le \sum_s g$ give $f(a) + \sum_s f \le g(a) + \sum_s g$. The second rule is the first with $f = 0$. For the third, use induction on $s$ with the triangle inequality: $|f(a) + \sum_s f| \le |f(a)| + |\sum_s f| \le |f(a)| + \sum_s |f|$. $\square$

::: mathlib
`Finset.sum_le_sum` · `Mathlib.Algebra.Order.BigOperators.Group.Finset`

The hypothesis is `∀ i ∈ s, f i ≤ g i`, so the inequality is only needed on `s`. The tactic `gcongr` applies it and leaves the goal `f i ≤ g i` with `i ∈ s` in the context.

<?decl Finset.sum_le_sum?>
:::

**Theorem (Cauchy-Schwarz).** Let $s$ be a finset and $f, g : \iota \to \mathbb{R}$. Then $$\Bigl(\sum_{i \in s} f(i) g(i)\Bigr)^2 \le \Bigl(\sum_{i \in s} f(i)^2\Bigr) \Bigl(\sum_{i \in s} g(i)^2\Bigr).$$

*Proof.* Put $A = \sum_s f^2$, $B = \sum_s f g$ and $C = \sum_s g^2$. The claim is $B^2 \le A C$. Each $f(i)^2 \ge 0$, so $A \ge 0$.

Case $A = 0$. A sum of nonnegative terms is zero only if each term is zero, so $f(i) = 0$ for each $i \in s$. Then $B = 0$, and $B^2 = 0 \le 0 = AC$.

Case $A > 0$. For each $i$, $(A g(i) - B f(i))^2 \ge 0$. Sum over $s$ and expand with the linear rules: $$0 \le \sum_{i \in s} \bigl(A g(i) - B f(i)\bigr)^2 = A^2 \sum_s g^2 - 2AB \sum_s f g + B^2 \sum_s f^2 = A^2 C - 2 A B^2 + A B^2 = A (A C - B^2).$$ Divide by $A > 0$: $0 \le AC - B^2$. $\square$

The proof also gives the case of equality. If $A > 0$ and $B^2 = AC$, then each $A g(i) - B f(i)$ is zero, so $g$ is the multiple $(B/A) f$ on $s$.

::: mathlib
`Finset.sum_mul_sq_le_sq_mul_sq` · `Mathlib.Algebra.Order.BigOperators.Ring.Finset`

Mathlib states the inequality for a commutative semiring with a linear order that is a strictly ordered ring and has `ExistsAddOfLE`. So one proof covers `ℕ`, `ℤ`, `ℚ` and `ℝ`. The form for a real inner product space is `real_inner_mul_inner_self_le`.

<?decl Finset.sum_mul_sq_le_sq_mul_sq?>
:::

**Theorem (Sums of an if).** For a decidable predicate $p$ and $f, g : \iota \to M$, $$\sum_{x \in s} \bigl(\text{if } p(x) \text{ then } f(x) \text{ else } g(x)\bigr) = \sum_{x \in s,\ p(x)} f(x) + \sum_{x \in s,\ \neg p(x)} g(x).$$ In particular, in a semiring, $\sum_{x \in s} (\text{if } p(x) \text{ then } 1 \text{ else } 0) = |\{x \in s : p(x)\}|$.

*Proof.* Split $s$ by $p$ with the splitting rule. On the filter for $p$, the term is $f(x)$. On the filter for $\neg p$, the term is $g(x)$. Change the terms on each part. For the second claim, take $f = 1$ and $g = 0$: the first sum is the card of the filter, by the card as a sum, and the second sum is $0$. $\square$

::: mathlib
`Finset.sum_ite` · `Mathlib.Algebra.BigOperators.Group.Finset.Piecewise`

The split of a sum of an `if`. The special forms `Finset.sum_ite_eq` and `Finset.sum_ite_eq'` give `∑ x ∈ s, if a = x then f x else 0 = if a ∈ s then f a else 0`, a sum with one nonzero term. They are `simp` lemmas.

<?decl Finset.sum_ite?>
:::

### Examples

**Example (Gauss by reflection).** Let $S = \sum_{j < n} j$. The rule of reflection gives $S = \sum_{j < n} (n - 1 - j)$. Add the two forms: $2S = \sum_{j < n} (n - 1) = n(n - 1)$, because $j + (n - 1 - j) = n - 1$ for $j \le n - 1$, also in $\mathbb{N}$.

**Example (A telescope).** For $n \ge 1$, $\sum_{k=1}^{n} \frac{1}{k(k + 1)} = 1 - \frac{1}{n + 1}$, because $\frac{1}{k(k + 1)} = \frac{1}{k} - \frac{1}{k + 1}$. Use $f(i) = -\frac{1}{i + 1}$ in $\mathbb{Q}$. Then $f(i + 1) - f(i) = \frac{1}{i + 1} - \frac{1}{i + 2} = \frac{1}{(i + 1)(i + 2)}$, and the telescope gives $\sum_{i < n} \frac{1}{(i + 1)(i + 2)} = f(n) - f(0) = 1 - \frac{1}{n + 1}$. For $n = 4$: $\frac{1}{2} + \frac{1}{6} + \frac{1}{12} + \frac{1}{20} = \frac{30 + 10 + 5 + 3}{60} = \frac{48}{60} = \frac{4}{5}$.

**Example (A geometric sum).** For $x = 3$ and $n = 5$: $1 + 3 + 9 + 27 + 81 = 121$, and $\frac{3^5 - 1}{3 - 1} = \frac{242}{2} = 121$. In $\mathbb{N}$, the form with no division is $2 \sum_{i < 5} 3^i + 1 = 3^5$.

**Example (Exchange over a triangle).** Let $H_k = \sum_{j=1}^{k} \frac{1}{j}$ be the harmonic numbers. Then $\sum_{k=1}^{n} H_k = (n + 1) H_n - n$. The double sum $\sum_{k=1}^{n} \sum_{j=1}^{k} \frac{1}{j}$ is a sum over the triangle $\{(k, j) : 1 \le j \le k \le n\}$. For a fixed $j$, the values of $k$ are $j, j + 1, \ldots, n$, and there are $n - j + 1$ of them. So the exchange gives $$\sum_{k=1}^{n} H_k = \sum_{j=1}^{n} \frac{n - j + 1}{j} = (n + 1) \sum_{j=1}^{n} \frac{1}{j} - \sum_{j=1}^{n} 1 = (n + 1) H_n - n.$$ For $n = 3$: $H_1 + H_2 + H_3 = 1 + \frac{3}{2} + \frac{11}{6} = \frac{13}{3}$, and $4 \cdot \frac{11}{6} - 3 = \frac{22}{3} - 3 = \frac{13}{3}$.

**Example (Cauchy-Schwarz with numbers).** For $f = (1, 2, 3)$ and $g = (4, 5, 6)$: $B = 4 + 10 + 18 = 32$, $A = 1 + 4 + 9 = 14$ and $C = 16 + 25 + 36 = 77$. So $B^2 = 1024 \le 1078 = AC$.

**Example (Order).** A term by term inequality gives an inequality of the sums.

<?lean MathlibHandbook/V03/C06/Examples.lean#le?>

**Counterexample (Reindexing needs injectivity).** Let $s = \{0, 1\}$, $t = \{0\}$, $i(a) = 0$ and $f = g = 1$. The map $i$ sends $s$ onto $t$, but it is not injective on $s$. The sums are $\sum_s f = 2$ and $\sum_t g = 1$. So the hypothesis of injectivity can not be dropped.

### Common errors

- A reindexing map in `ℕ` with a subtraction is a bijection only on the right finset. The proof of each condition of `Finset.sum_nbij'` must use the hypothesis `a ∈ s`, often in the form `a < n`, before `omega` can close it.
- The telescope `Finset.sum_range_sub` needs a group. In `ℕ`, cast to `ℤ` first, or prove the form with a sum on both sides.
- For $x = 1$, the quotient $\frac{x^n - 1}{x - 1}$ has the junk value $0$ in Mathlib, and the true sum is $n$. So `geom_sum_eq` needs $x \ne 1$.

### The library around it

The rules come in families with a fixed naming pattern: reindexing (`sum_bij`, `sum_nbij'`, `sum_equiv`, `sum_image`), splitting (`sum_union`, `sum_sdiff`, `sum_range_add`), exchange (`sum_product`, `sum_sigma`, `sum_comm`), ranges (`sum_range_reflect`), sums of an `if` (`sum_ite`, `sum_ite_eq`) and order (`sum_le_sum`, `sum_nonneg`, `abs_sum_le_sum_abs`), all in the namespace `Finset`. Each rule has a product twin, with `prod` for `sum`. The table below lists the declarations of the files of this section.

### Exercises

1. (A) Compute $\sum_{i < 4} \sum_{j < 3} i j$ in both orders, and with the rule $\sum_i \sum_j a_i b_j = (\sum_i a_i)(\sum_j b_j)$.
2. (A) Give finsets $s_1, s_2$ and an $f$ with $\sum_{s_1 \cup s_2} f \ne \sum_{s_1} f + \sum_{s_2} f$.
3. (B) Prove $\sum_{k=1}^{n} k \cdot 2^{k} = (n - 1) 2^{n + 1} + 2$ with a telescope. Hint: find $F$ with $F(k + 1) - F(k) = (k + 1) 2^{k + 1}$ of the form $F(k) = (ak + b) 2^{k}$.
4. (B) Prove $\sum_{i < n} \sum_{j < i} 1 = \sum_{j < n} (n - 1 - j)$ by the exchange over a triangle, and deduce the formula of Gauss a third time.
5. (B) Let $a_1, \ldots, a_n > 0$ be real. Prove $\bigl(\sum a_i\bigr)\bigl(\sum 1/a_i\bigr) \ge n^2$. Hint: Cauchy-Schwarz with $f = \sqrt{a}$ and $g = 1/\sqrt{a}$.
6. (B) Prove that $\prod_{k=2}^{n} \bigl(1 - \frac{1}{k^2}\bigr) = \frac{n + 1}{2n}$ for $n \ge 2$, with the telescope of quotients. Hint: $1 - \frac{1}{k^2} = \frac{k - 1}{k} \cdot \frac{k + 1}{k}$.
7. (C) Prove the identity of Lagrange: $\bigl(\sum f^2\bigr)\bigl(\sum g^2\bigr) - \bigl(\sum f g\bigr)^2 = \frac{1}{2} \sum_{i, j \in s} \bigl(f(i) g(j) - f(j) g(i)\bigr)^2$, and derive Cauchy-Schwarz from it with no case split.

### Notes and history

The finite exchange of the order of summation needs no hypothesis. The inequality of Cauchy and Schwarz for finite sums is in Cauchy's *Cours d'analyse* (1821). Bunyakovsky (1859) and Schwarz (1888) proved the form for integrals. Graham, Knuth and Patashnik, *Concrete Mathematics*, Sections 2.3 to 2.6, treat these moves in the same order.

In Mathlib, the dependent `Finset.sum_bij` is the old form, and the forms `Finset.sum_nbij` and `Finset.sum_nbij'` with plain maps were added later, because most maps in practice are plain. The order lemmas live in the folder `Mathlib/Algebra/Order/BigOperators`, so that a file that needs only the algebra does not import the order theory.

### Reference

<?reference?>
