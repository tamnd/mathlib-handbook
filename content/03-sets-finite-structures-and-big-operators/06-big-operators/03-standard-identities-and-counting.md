---
title: Standard identities and counting with sums
kind: theory
modules:
  - Mathlib.Algebra.BigOperators.Ring.Finset
  - Mathlib.Algebra.BigOperators.Group.Finset.Powerset
explains:
  E3: [Finset.prod_one_add, Finset.card_eq_sum_card_fiberwise]
  E2: [Finset.prod_add, Finset.sum_pow_mul_eq_add_pow, Finset.sum_powerset, Finset.sum_fiberwise, Finset.card_eq_sum_card_image, Finset.prod_one_sub_ordered]
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

## Standard identities and counting with sums

### Overview

This section uses the algebra of Section 2 for the standard identities: the binomial theorem, the sums of a row of the triangle of Pascal, and the closed forms of $\sum k$, $\sum k^2$ and $\sum k^3$. It then turns to counting. A count is a sum of ones, so the rules of sums become rules of counting. Double counting is the exchange of two sums, and the principle of inclusion and exclusion is the expansion of a product $\prod (1 - x_i)$. The number of derangements is a first application.

The main theorems are the binomial theorem $(x + y)^n = \sum_{k} \binom{n}{k} x^k y^{n - k}$, the rule of double counting and the formula of inclusion and exclusion $$\Bigl|\bigcup_{i \in I} A_i\Bigr| = \sum_{\emptyset \ne T \subseteq I} (-1)^{|T| + 1} \Bigl|\bigcap_{i \in T} A_i\Bigr|.$$ The binomial coefficients are in Volume 2 and in Chapter 3. This section needs only their definition as a count of subsets, and it proves the rule of Pascal.

### Definitions

**Definition (Binomial coefficient).** For $n, k \in \mathbb{N}$, the binomial coefficient $\binom{n}{k}$ is the number of subsets with $k$ elements of a set with $n$ elements. A bijection between two such sets shows that the number does not depend on the set. So $\binom{n}{0} = \binom{n}{n} = 1$, $\binom{n}{1} = n$, and $\binom{n}{k} = 0$ for $k > n$.

*Remark.* Mathlib defines `Nat.choose` by the recursion of Pascal. The theorem `Finset.card_powersetCard` says that `Finset.powersetCard k s`, the finset of the `k`-subsets of `s`, has card `s.card.choose k`. So the two definitions agree.

::: mathlib
`Nat.choose` · `Mathlib.Data.Nat.Choose.Basic`

Defined by `choose _ 0 = 1`, `choose 0 (k + 1) = 0` and `choose (n + 1) (k + 1) = choose n k + choose n (k + 1)`, in Volume 2. The value for `k > n` is `0`.

<?decl Nat.choose?>
:::

**Definition (Indicator).** For a subset $A$ of a set $U$, the indicator $1_A : U \to \mathbb{Z}$ has $1_A(x) = 1$ for $x \in A$ and $1_A(x) = 0$ for $x \notin A$. Then $1_{A \cap B} = 1_A \cdot 1_B$, $1_{U \setminus A} = 1 - 1_A$, and $|A| = \sum_{x \in U} 1_A(x)$.

**Definition (Derangement).** A *derangement* of a finite set $X$ is a permutation $\sigma$ of $X$ with $\sigma(x) \ne x$ for each $x \in X$. The number of derangements of a set with $n$ elements is $D_n$. So $D_0 = 1$, $D_1 = 0$, $D_2 = 1$ and $D_3 = 2$.

### Theorems and proofs

**Theorem (Pascal).** For $n, k \in \mathbb{N}$, $\binom{n + 1}{k + 1} = \binom{n}{k} + \binom{n}{k + 1}$.

*Proof.* Let $X$ be a set with $n$ elements, and let $a \notin X$. A $(k + 1)$-subset $S$ of $X \cup \{a\}$ with $a \notin S$ is a $(k + 1)$-subset of $X$, and there are $\binom{n}{k + 1}$ of them. For the subsets $S$ with $a \in S$, the map $S \mapsto S \setminus \{a\}$ is a bijection onto the $k$-subsets of $X$, with inverse $S' \mapsto S' \cup \{a\}$. So there are $\binom{n}{k}$ of them. The two kinds are disjoint and cover all the $(k + 1)$-subsets. $\square$

**Theorem (Binomial theorem).** Let $R$ be a commutative semiring, $x, y \in R$ and $n \in \mathbb{N}$. Then $$(x + y)^n = \sum_{m=0}^{n} \binom{n}{m} x^m y^{n - m}.$$

*Proof.* Use induction on $n$. For $n = 0$, both sides are $1$. Assume the formula for $n$. Multiply it by $x + y$: $$(x + y)^{n + 1} = \sum_{m=0}^{n} \binom{n}{m} x^{m + 1} y^{n - m} + \sum_{m=0}^{n} \binom{n}{m} x^m y^{n + 1 - m}.$$ In the first sum, put $j = m + 1$, so the term is $\binom{n}{j - 1} x^{j} y^{n + 1 - j}$ for $1 \le j \le n + 1$. To the second sum, add the term for $m = n + 1$, which is $0$. The term $j = 0$ of the second sum is $y^{n + 1} = \binom{n + 1}{0} y^{n + 1}$. For $1 \le j \le n + 1$, the coefficient of $x^j y^{n + 1 - j}$ is $\binom{n}{j - 1} + \binom{n}{j} = \binom{n + 1}{j}$, by the rule of Pascal. $\square$

The proof uses $x^{m} y^{n - m} \cdot x = x^{m + 1} y^{n - m}$, so it needs $x y = y x$.

::: mathlib
`add_pow` · `Mathlib.Data.Nat.Choose.Sum`

The coefficient is on the right, cast from `ℕ` to `R`. The form for a semiring with `Commute x y` is `Commute.add_pow`. The file is in Volume 2.

<?decl add_pow?>
:::

The next theorem is the form of the binomial theorem with subsets. Each term of the expansion of $\prod (1 + f(i))$ chooses $1$ or $f(i)$ in each factor, and the set $t$ of the indices where it chose $f(i)$ determines the term.

**Theorem (Expansion of a product).** Let $R$ be a commutative semiring, $s$ a finset and $f : \iota \to R$. Then $$\prod_{i \in s} \bigl(1 + f(i)\bigr) = \sum_{t \subseteq s} \prod_{i \in t} f(i).$$

*Proof.* Use induction on $s$. For $s = \emptyset$, both sides are $1$. Let $a \notin s$, and assume the formula for $s$. The subsets of $s \cup \{a\}$ are the subsets $t$ of $s$ and the sets $t \cup \{a\}$ with $t \subseteq s$. The two families are disjoint, and $t \mapsto t \cup \{a\}$ is injective on the subsets of $s$. For $t \subseteq s$, $\prod_{t \cup \{a\}} f = f(a) \prod_t f$. With the splitting rule and the sum over an image (Section 2), $$\sum_{t \subseteq s \cup \{a\}} \prod_{t} f = \sum_{t \subseteq s} \prod_{t} f + f(a) \sum_{t \subseteq s} \prod_{t} f = (1 + f(a)) \prod_{i \in s} (1 + f(i)).$$ $\square$

::: mathlib
`Finset.prod_one_add` · `Mathlib.Algebra.BigOperators.Ring.Finset`

The general form `Finset.prod_add` expands $\prod_{s} (f + g) = \sum_{t \subseteq s} \prod_{t} f \cdot \prod_{s \setminus t} g$. The form `Finset.sum_pow_mul_eq_add_pow` is the binomial theorem with subsets: $\sum_{t \subseteq s} a^{|t|} b^{|s| - |t|} = (a + b)^{|s|}$.

<?decl Finset.prod_one_add?>
:::

**Theorem (Rows of Pascal).** For each $n$, $\sum_{k=0}^{n} \binom{n}{k} = 2^n$. For $n \ge 1$, $\sum_{k=0}^{n} (-1)^k \binom{n}{k} = 0$.

*Proof.* Put $x = y = 1$ in the binomial theorem for the first claim. Put $x = -1$ and $y = 1$ in $\mathbb{Z}$ for the second: the sum is $(-1 + 1)^n = 0^n = 0$, since $n \ge 1$. $\square$

The first claim also has a proof by counting: both sides count the subsets of a set with $n$ elements, and the left side groups them by their card. `Finset.sum_powerset` is this regrouping for any sum over `s.powerset`.

::: mathlib
`Nat.sum_range_choose` · `Mathlib.Data.Nat.Choose.Sum`

The alternating sum is `Int.alternating_sum_range_choose`, with the value `if n = 0 then 1 else 0`.

<?decl Nat.sum_range_choose?>
:::

**Theorem (Hockey stick).** For $n, m \in \mathbb{N}$, $\sum_{k=0}^{n} \binom{k}{m} = \binom{n + 1}{m + 1}$.

*Proof.* Use induction on $n$. For $n = 0$, the left side is $\binom{0}{m}$, which is $1$ for $m = 0$ and $0$ otherwise. The right side $\binom{1}{m + 1}$ has the same values. If the formula holds for $n$, then $\sum_{k=0}^{n + 1} \binom{k}{m} = \binom{n + 1}{m + 1} + \binom{n + 1}{m} = \binom{n + 2}{m + 1}$, by the rule of Pascal. $\square$

**Theorem (Sums of powers).** For each $n$, $$\sum_{k=0}^{n} k = \binom{n + 1}{2}, \qquad \sum_{k=0}^{n} k^2 = 2 \binom{n + 1}{3} + \binom{n + 1}{2}, \qquad \sum_{k=0}^{n} k^3 = \Bigl(\sum_{k=0}^{n} k\Bigr)^2.$$

*Proof.* For each $k$, $k = \binom{k}{1}$ and $k^2 = 2 \binom{k}{2} + \binom{k}{1}$. The hockey stick with $m = 1$ and $m = 2$ gives the first two formulas. For the third, put $T_n = \frac{n(n + 1)}{2}$. For $n \ge 1$, $$T_n^2 - T_{n - 1}^2 = \frac{n^2 \bigl((n + 1)^2 - (n - 1)^2\bigr)}{4} = n^3.$$ Since $T_0^2 = 0$, induction on $n$ gives $T_n^2 = \sum_{k=0}^{n} k^3$. $\square$

For $n = 4$: $2 \cdot 10 + 10 = 30 = 1 + 4 + 9 + 16$. For $n = 3$: $1 + 8 + 27 = 36 = (1 + 2 + 3)^2$.

**Theorem (Counting by fibers).** Let $f : \iota \to \kappa$, and let $s, t$ be finsets with $f(a) \in t$ for each $a \in s$. The *fiber* of $b$ is $\{a \in s : f(a) = b\}$. Then $$|s| = \sum_{b \in t} \bigl|\{a \in s : f(a) = b\}\bigr|.$$

*Proof.* For $a \in s$, exactly one $b \in t$ has $f(a) = b$, so $1 = \sum_{b \in t} [f(a) = b]$, where $[P]$ is $1$ if $P$ holds and $0$ otherwise. Exchange the two sums by the theorem of Fubini: $$|s| = \sum_{a \in s} \sum_{b \in t} [f(a) = b] = \sum_{b \in t} \sum_{a \in s} [f(a) = b] = \sum_{b \in t} \bigl|\{a \in s : f(a) = b\}\bigr|.$$ The last step is the sum of an if of Section 2. $\square$

::: mathlib
`Finset.card_eq_sum_card_fiberwise` · `Mathlib.Algebra.BigOperators.Group.Finset.Basic`

The hypothesis is `Set.MapsTo f s t`. `Finset.card_eq_sum_card_image` takes `t = s.image f`, and `Finset.sum_fiberwise` is the same rule for a sum of any `g`.

<?decl Finset.card_eq_sum_card_fiberwise?>
:::

**Theorem (Double counting).** Let $s$ be a finset of $\alpha$, $t$ a finset of $\beta$, and $R$ a decidable relation between $\alpha$ and $\beta$. Then $$\sum_{a \in s} \bigl|\{b \in t : a \mathrel{R} b\}\bigr| = \sum_{b \in t} \bigl|\{a \in s : a \mathrel{R} b\}\bigr|.$$

*Proof.* By the sum of an if, the left side is $\sum_{a \in s} \sum_{b \in t} [a \mathrel{R} b]$. Exchange the sums by the theorem of Fubini, and apply the sum of an if again. $\square$

::: mathlib
`Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow` · `Mathlib.Combinatorics.Enumerative.DoubleCounting`

Here `Finset.bipartiteAbove r t a` is $\{b \in t : r\,a\,b\}$ and `Finset.bipartiteBelow r s b` is $\{a \in s : r\,a\,b\}$. The file is in Volume 30, on combinatorics, with the forms with inequalities.

<?decl Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow?>
:::

**Theorem (Handshake).** Let $G$ be a finite graph with vertex set $V$ and edge set $E$, where each edge is a set of two vertices. For $v \in V$, let $\deg v$ be the number of edges that contain $v$. Then $\sum_{v \in V} \deg v = 2 |E|$. So the number of vertices of odd degree is even.

*Proof.* Apply double counting to $s = V$, $t = E$ and the relation $v \in e$. A vertex $v$ has $\deg v$ partners, and an edge $e$ has $|e| = 2$. So $\sum_v \deg v = 2|E|$. The sum over the vertices of even degree is even, so the sum over the $r$ vertices of odd degree is even, and this sum has the parity of $r$. $\square$

In Mathlib, the handshake is `SimpleGraph.sum_degrees_eq_twice_card_edges`, in the volume on combinatorics.

**Theorem (Inclusion and exclusion).** Let $U$ be a finite set, $I$ a finite set of indices and $A_i \subseteq U$ for $i \in I$. For $T \subseteq I$, put $A_T = \bigcap_{i \in T} A_i$, with $A_\emptyset = U$. Then $$\Bigl|U \setminus \bigcup_{i \in I} A_i\Bigr| = \sum_{T \subseteq I} (-1)^{|T|} |A_T|, \qquad \Bigl|\bigcup_{i \in I} A_i\Bigr| = \sum_{\emptyset \ne T \subseteq I} (-1)^{|T| + 1} |A_T|.$$

*Proof.* Fix $x \in U$. The expansion of a product with $f(i) = -1_{A_i}(x)$ and $\prod_{i \in T} 1_{A_i} = 1_{A_T}$ give $$\prod_{i \in I} \bigl(1 - 1_{A_i}(x)\bigr) = \sum_{T \subseteq I} (-1)^{|T|} 1_{A_T}(x).$$ The left side is $1$ if $x$ lies in no $A_i$, and $0$ otherwise. Sum over $x \in U$, and exchange the sums on the right by the theorem of Fubini: $$\Bigl|U \setminus \bigcup_{i} A_i\Bigr| = \sum_{T \subseteq I} (-1)^{|T|} \sum_{x \in U} 1_{A_T}(x) = \sum_{T \subseteq I} (-1)^{|T|} |A_T|.$$ For the second formula, $|\bigcup A_i| = |U| - |U \setminus \bigcup A_i|$, and the term of $T = \emptyset$ in the first formula is $|U|$. $\square$

For two sets, the formula is $|A \cup B| = |A| + |B| - |A \cap B|$, the rule of Chapter 3.

::: mathlib
`Finset.inclusion_exclusion_card_inf_compl` · `Mathlib.Combinatorics.Enumerative.InclusionExclusion`

The first formula, for finsets `S i` of a `Fintype α`, with the intersection `t.inf S`. The second is `Finset.inclusion_exclusion_card_biUnion`. The file is in the volume on combinatorics.

<?decl Finset.inclusion_exclusion_card_inf_compl?>
:::

**Theorem (Derangements).** For each $n$, $$D_n = \sum_{k=0}^{n} (-1)^k \binom{n}{k} (n - k)! = \sum_{k=0}^{n} (-1)^k \frac{n!}{k!}.$$

*Proof.* Let $U$ be the set of the permutations of $X = \{1, \ldots, n\}$, and let $A_i = \{\sigma \in U : \sigma(i) = i\}$. Then $D_n = |U \setminus \bigcup A_i|$. A permutation in $A_T$ fixes $T$, so it maps $X \setminus T$ onto itself. Restriction is a bijection from $A_T$ to the permutations of $X \setminus T$, with the inverse that extends by the identity on $T$. So $|A_T| = (n - |T|)!$. There are $\binom{n}{k}$ sets $T$ with $|T| = k$. Inclusion and exclusion with the terms grouped by $k$ gives the first formula, and $\binom{n}{k} (n - k)! = \frac{n!}{k!}$ gives the second. $\square$

So $\frac{D_n}{n!}$ is a partial sum of the series of $e^{-1}$, and for large $n$ about $37\%$ of the permutations are derangements.

::: mathlib
`numDerangements_sum` · `Mathlib.Combinatorics.Derangements.Finite`

Mathlib defines `numDerangements` by the recursion $D_{n + 2} = (n + 1)(D_n + D_{n + 1})$, and `card_derangements_eq_numDerangements` connects it to the count. The closed form is in `ℤ`.

<?decl numDerangements_sum?>
:::

### Examples

**Example (A row of Pascal).** For $n = 4$: $(x + y)^4 = x^4 + 4x^3 y + 6 x^2 y^2 + 4 x y^3 + y^4$. The coefficients add to $16 = 2^4$, and $1 - 4 + 6 - 4 + 1 = 0$.

**Example (Divisors by double counting).** Let $d(n)$ be the number of divisors of $n$. Double counting to $s = t = \{1, \ldots, N\}$ and the relation $a \mid b$ gives $\sum_{b=1}^{N} d(b) = \sum_{a=1}^{N} \lfloor N/a \rfloor$. For $N = 6$, the left side is $1 + 2 + 2 + 3 + 2 + 4 = 14$, and the right side is $6 + 3 + 2 + 1 + 1 + 1 = 14$.

**Example (Handshake).** The complete graph $K_4$ has $4$ vertices of degree $3$ and $\binom{4}{2} = 6$ edges. The sum of the degrees is $12 = 2 \cdot 6$. No graph has the degrees $3, 3, 3$, because the sum $9$ is odd.

**Example (The totient by inclusion and exclusion).** Count the $x \in U = \{1, \ldots, 30\}$ that are prime to $30 = 2 \cdot 3 \cdot 5$. Let $A_p$ be the multiples of $p$ in $U$. Then $|A_2| = 15$, $|A_3| = 10$, $|A_5| = 6$, $|A_2 \cap A_3| = 5$, $|A_2 \cap A_5| = 3$, $|A_3 \cap A_5| = 2$ and $|A_2 \cap A_3 \cap A_5| = 1$. The first formula gives $30 - 31 + 10 - 1 = 8$. So $\varphi(30) = 8$.

**Example (Derangements of four and five points).** $D_4 = 24 - 24 + 12 - 4 + 1 = 9$. A direct check: a derangement of four points is a product of two disjoint transpositions ($3$ of them) or a $4$-cycle ($3! = 6$). $D_5 = 120 - 120 + 60 - 20 + 5 - 1 = 44$. A direct check: a $5$-cycle ($4! = 24$) or a transposition times a disjoint $3$-cycle ($\binom{5}{2} \cdot 2 = 20$). The recursion agrees: $D_4 = 3(D_2 + D_3) = 9$ and $D_5 = 4(D_3 + D_4) = 44$.

**Example (A count as a sum).** The card of a finset is the sum of ones, the first step of each proof above.

<?lean MathlibHandbook/V03/C06/Examples.lean#card?>

**Counterexample (No commutativity).** For the $2 \times 2$ matrices $A = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$ and $B = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix}$, $A^2 = B^2 = 0$ and $AB + BA = I$. So $(A + B)^2 = I$, but $A^2 + 2AB + B^2 = \begin{pmatrix} 2 & 0 \\ 0 & 0 \end{pmatrix}$. The binomial theorem fails, because $AB \ne BA$.

### Common errors

- The binomial theorem in Mathlib has the coefficient last and the power of $x$ first: `x ^ m * y ^ (n - m) * n.choose m`. A goal with the coefficient first needs `mul_comm` or `ring_nf` before `rw [add_pow]`.
- Inclusion and exclusion has signs, so the formula lives in `ℤ`, not in `ℕ`. The Mathlib forms state it with a cast of the card to `ℤ`.

### The library around it

The file `Mathlib.Algebra.BigOperators.Ring.Finset` has the rules that mix sums and products: `Finset.sum_mul_sum`, `Finset.prod_add`, `Finset.prod_one_add`, `Finset.prod_univ_sum`, and `Finset.prod_one_sub_ordered`, which expands a product of differences in a fixed order. The identities of the binomial coefficients are in Volume 2, and the counting files are in the volume on combinatorics. The table below lists the declarations of the two files of this section.

### Exercises

1. (A) Expand $(2x - 1)^5$ with the binomial theorem, and check the sum of the coefficients at $x = 1$.
2. (A) Use the hockey stick to compute $\sum_{k=0}^{10} \binom{k}{3}$.
3. (A) How many $x \in \{1, \ldots, 100\}$ are divisible by none of $2$, $3$ and $7$? Use inclusion and exclusion.
4. (B) Prove the identity of Vandermonde $\binom{m + n}{k} = \sum_{j=0}^{k} \binom{m}{j} \binom{n}{k - j}$ by counting the $k$-subsets of a disjoint union $X \cup Y$ by the size of their part in $X$.
5. (B) Prove $\sum_{k=0}^{n} k \binom{n}{k} = n 2^{n - 1}$ for $n \ge 1$ by double counting the pairs $(x, S)$ with $x \in S \subseteq \{1, \ldots, n\}$.
6. (B) Prove that the number of surjections from a set with $n$ elements onto a set with $m$ elements is $\sum_{k=0}^{m} (-1)^k \binom{m}{k} (m - k)^n$. Hint: let $A_i$ be the maps that miss $i$.
7. (C) Prove the recursion $D_{n + 2} = (n + 1)(D_n + D_{n + 1})$ by counting: classify a derangement $\sigma$ of $\{0, \ldots, n + 1\}$ by $j = \sigma(n + 1)$ and by whether $\sigma(j) = n + 1$.

### Notes and history

The triangle of the binomial coefficients was known to Pingala, to al-Karaji and Omar Khayyam and to Yang Hui, long before the *Traité du triangle arithmétique* of Pascal (1654). Newton extended the binomial theorem to real exponents. Sylvester stated inclusion and exclusion in its general form in 1883. The *problème des rencontres* of the derangements is due to Montmort (1708). The handshake lemma is in the paper of Euler (1736) on the bridges of Königsberg. Stanley, *Enumerative Combinatorics*, Volume 1, Chapter 2, treats these methods.

### Reference

<?reference?>
