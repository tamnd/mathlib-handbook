---
title: Subsets of a given size and the binomial coefficients
kind: theory
modules:
  - Mathlib.Data.Finset.Powerset
explains:
  E3: [Finset.powersetCard, Finset.card_powersetCard]
  E2: [Finset.mem_powersetCard, Finset.powersetCard_succ_insert, Finset.powersetCard_eq_empty, Finset.powerset_card_disjiUnion]
  E1: auto
families: []
requires: [V03.C02, V02]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V03/C03/Examples.lean
  - MathlibHandbook/V03/C03/Exercises.lean
  - MathlibHandbook/V03/C03/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Subsets of a given size and the binomial coefficients

### Overview

Section 1 counted all the subsets of a finset: a finset with $n$ members has $2^n$ subsets. This section counts the subsets with exactly $k$ members. Their number is the binomial coefficient $\binom{n}{k}$, read "$n$ choose $k$". The binomial coefficients answer the questions "how many committees of $3$ can a group of $10$ form" and "how many tickets has a lottery that draws $6$ numbers of $49$".

Mathlib defines the number $\binom{n}{k}$ by the rule of Pascal, with no reference to sets, and the finset `Finset.powersetCard k s` of the $k$-subsets separately. The main theorem connects the two. From it the section proves the symmetry, the factorial formula, the sum of a row and the identity of Vandermonde, each by counting one finset in two ways.

The binomial theorem $(x + y)^n = \sum_k \binom{n}{k} x^k y^{n-k}$ uses sums over finsets. It is in Section 3 of Chapter 6, together with the other identities with sums.

### Definitions

**Definition (Binomial coefficient).** For $n, k \in \mathbb{N}$ the number $\binom{n}{k}$ is defined by recursion: $$\binom{n}{0} = 1, \qquad \binom{0}{k+1} = 0, \qquad \binom{n+1}{k+1} = \binom{n}{k} + \binom{n}{k+1}.$$

The third equation is the rule of Pascal. The recursion is on $n$, and each value of row $n + 1$ comes from two values of row $n$. So the definition gives one number for each pair $(n, k)$. A short induction on $n$ gives two facts that the proofs below use.

1. $\binom{n}{k} = 0$ for $k > n$. For $n = 0$ this is the second equation. For $n + 1$ and $k + 1 > n + 1$, both $k > n$ and $k + 1 > n$, so both terms of the rule of Pascal are $0$.
2. $\binom{n}{n} = 1$. For $n = 0$ this is the first equation. For $n + 1$, $\binom{n+1}{n+1} = \binom{n}{n} + \binom{n}{n+1} = 1 + 0$, by the hypothesis of induction and fact 1.

::: mathlib
`Nat.choose` · `Mathlib.Data.Nat.Choose.Basic`

`Nat.choose n k` is defined by the three equations above, by pattern matching. The rule of Pascal is `Nat.choose_succ_succ`, and the two facts are `Nat.choose_eq_zero_of_lt` and `Nat.choose_self`. The value $0$ for $k > n$ is not a junk value: it is the number of $k$-subsets of an $n$-set. The file belongs to Volume 2.

<?decl Nat.choose?>
:::

**Definition (Subsets of a given size).** Let $s$ be a finset and $k \in \mathbb{N}$. The finset $\mathcal{P}_k(s)$ is the finset of the subsets $u \subseteq s$ with $|u| = k$.

So $\mathcal{P}_k(s) = \{u \in \mathcal{P}(s) : |u| = k\}$, a filter of the power set. A subset of $s$ with $k$ members is a $k$-subset of $s$.

::: mathlib
`Finset.powersetCard` · `Mathlib.Data.Finset.Powerset`

`Finset.powersetCard k s` is a `Finset (Finset α)`. Mathlib defines it from `Multiset.powersetCard`, which builds the sublists of length $k$ by a recursion that follows the rule of Pascal, so it needs no `DecidableEq α`. The form as a filter is `Finset.powersetCard_eq_filter`, and the membership rule is `Finset.mem_powersetCard`: `u ∈ powersetCard k s ↔ u ⊆ s ∧ #u = k`.

<?decl Finset.powersetCard?>
:::

### Theorems and proofs

The first theorem is the analogue for $\mathcal{P}_k$ of the decomposition of the power set in Section 1.

**Theorem (Pascal for subsets).** Let $a \notin s$ and $k \in \mathbb{N}$. Then $\mathcal{P}_{k+1}(s \cup \{a\})$ is the disjoint union of $\mathcal{P}_{k+1}(s)$ and of the image of $\mathcal{P}_k(s)$ under the map $v \mapsto v \cup \{a\}$. The map is injective on $\mathcal{P}_k(s)$.

*Proof.* Let $u$ be a $(k+1)$-subset of $s \cup \{a\}$. If $a \notin u$, then $u \subseteq s$, so $u \in \mathcal{P}_{k+1}(s)$. If $a \in u$, put $v = u \setminus \{a\}$. Then $v \subseteq s$ and $|v| = |u| - 1 = k$, so $v \in \mathcal{P}_k(s)$, and $u = v \cup \{a\}$. Conversely, each member of $\mathcal{P}_{k+1}(s)$ is a $(k+1)$-subset of $s \cup \{a\}$. For $v \in \mathcal{P}_k(s)$, the finset $v \cup \{a\}$ is a subset of $s \cup \{a\}$, and $|v \cup \{a\}| = k + 1$ because $a \notin v$. So the two parts give exactly $\mathcal{P}_{k+1}(s \cup \{a\})$.

The parts do not meet: each finset $v \cup \{a\}$ contains $a$, and no subset of $s$ contains $a$. The map is injective on $\mathcal{P}_k(s)$: if $v \cup \{a\} = v' \cup \{a\}$ with $a \notin v$ and $a \notin v'$, remove $a$ from both sides to get $v = v'$. $\square$

::: mathlib
`Finset.powersetCard_succ_insert` · `Mathlib.Data.Finset.Powerset`

The equation of the theorem, with the hypothesis `x ∉ s`: `powersetCard n.succ (insert x s) = powersetCard n.succ s ∪ (powersetCard n s).image (insert x)`. The disjointness and the injectivity are not part of the statement. A proof that uses the lemma proves them as in the text.

<?decl Finset.powersetCard_succ_insert?>
:::

**Theorem (Count of the $k$-subsets).** Let $s$ be a finset with $|s| = n$. Then $|\mathcal{P}_k(s)| = \binom{n}{k}$ for every $k \in \mathbb{N}$.

*Proof.* Use induction on $s$, and prove the claim for all $k$ at each step.

Let $s = \emptyset$. The only subset of $\emptyset$ is $\emptyset$, with card $0$. So $\mathcal{P}_0(\emptyset) = \{\emptyset\}$ has $1 = \binom{0}{0}$ member, and $\mathcal{P}_{k+1}(\emptyset) = \emptyset$ has $0 = \binom{0}{k+1}$ members.

Let $a \notin s$ with $|s| = n$, and assume the claim for $s$ and all $k$. Then $|s \cup \{a\}| = n + 1$. For $k = 0$, the only $0$-subset of a finset is $\emptyset$, so $|\mathcal{P}_0(s \cup \{a\})| = 1 = \binom{n+1}{0}$. For $k + 1$, use the theorem of Pascal for subsets. The two parts do not meet, so the card is the sum of their cards. The map $v \mapsto v \cup \{a\}$ is injective on $\mathcal{P}_k(s)$, so the image has the card $|\mathcal{P}_k(s)|$. With the hypothesis of induction, $$|\mathcal{P}_{k+1}(s \cup \{a\})| = |\mathcal{P}_{k+1}(s)| + |\mathcal{P}_k(s)| = \binom{n}{k+1} + \binom{n}{k} = \binom{n+1}{k+1}.$$ The last step is the rule of Pascal. $\square$

::: mathlib
`Finset.card_powersetCard` · `Mathlib.Data.Finset.Powerset`

The statement is `#(powersetCard n s) = (#s).choose n`. It holds for all `n`, also for `n > #s`, where both sides are $0$. Mathlib proves it on the multiset: the multiset `Multiset.powersetCard` has the card `Nat.choose`, by an induction that follows the same rule of Pascal. The lemma `Finset.powersetCard_eq_empty` says `powersetCard n s = ∅ ↔ #s < n`.

<?decl Finset.card_powersetCard?>
:::

The remaining theorems are proofs by counting. Each finds a bijection between two finsets, or splits one finset in two ways.

**Theorem (Symmetry).** If $k \leq n$, then $\binom{n}{k} = \binom{n}{n-k}$.

*Proof.* Let $s$ be a finset with $n$ members, for example $\operatorname{range} n$. Define $c(u) = s \setminus u$ for $u \subseteq s$. For $u \in \mathcal{P}_k(s)$, the card of a subset of Section 1 gives $|s \setminus u| = |s| - |u| = n - k$. So $c$ maps $\mathcal{P}_k(s)$ to $\mathcal{P}_{n-k}(s)$. In the same way $c$ maps $\mathcal{P}_{n-k}(s)$ to $\mathcal{P}_{n-(n-k)}(s) = \mathcal{P}_k(s)$, because $k \leq n$. For $u \subseteq s$, $c(c(u)) = s \setminus (s \setminus u) = u$. So the two maps are inverse to each other, and $c$ is a bijection. Thus the two finsets have the same card, and the count of the $k$-subsets gives $\binom{n}{k} = \binom{n}{n-k}$. $\square$

::: mathlib
`Nat.choose_symm` · `Mathlib.Data.Nat.Choose.Basic`

The statement is `k ≤ n → n.choose (n - k) = n.choose k`. The hypothesis is needed, because `n - k` truncates in $\mathbb{N}$: the counterexample below shows it. Mathlib proves the lemma from the factorial formula, not by a bijection. Both proofs are correct; the library chooses the shorter one in its setting.

<?decl Nat.choose_symm?>
:::

**Theorem (Factorial formula).** If $k \leq n$, then $\binom{n}{k} \, k! \, (n-k)! = n!$. So $\binom{n}{k} = \dfrac{n!}{k! \, (n-k)!}$.

*Proof.* Use induction on $n$, for all $k \leq n$ at once. For $n = 0$, only $k = 0$ is possible, and $1 \cdot 1 \cdot 1 = 0!$.

Assume the claim for $n$ and all $k \leq n$. Let $k \leq n + 1$. If $k = 0$, the left side is $1 \cdot 1 \cdot (n+1)!$. If $k = n + 1$, it is $1 \cdot (n+1)! \cdot 1$, since $\binom{n+1}{n+1} = 1$. Now let $1 \leq k \leq n$. The rule of Pascal gives $\binom{n+1}{k} = \binom{n}{k-1} + \binom{n}{k}$. Multiply by $k! \, (n+1-k)!$ and treat the two terms apart.

For the first term, $k! = k \cdot (k-1)!$, and $n + 1 - k = n - (k-1)$. Since $k - 1 \leq n$, the hypothesis of induction gives $$\binom{n}{k-1} \, k! \, (n+1-k)! = k \cdot \binom{n}{k-1} (k-1)! \, (n-(k-1))! = k \cdot n!.$$ For the second term, $(n+1-k)! = (n+1-k) \cdot (n-k)!$, because $n + 1 - k \geq 1$. Since $k \leq n$, the hypothesis gives $$\binom{n}{k} \, k! \, (n+1-k)! = (n+1-k) \cdot \binom{n}{k} k! \, (n-k)! = (n+1-k) \cdot n!.$$ The sum is $(k + n + 1 - k) \cdot n! = (n+1) \cdot n! = (n+1)!$. $\square$

The second form divides by $k! \, (n-k)!$, which is not $0$. In $\mathbb{N}$ the division is exact here, because the first form shows that $k! \, (n-k)!$ divides $n!$.

::: mathlib
`Nat.choose_mul_factorial_mul_factorial` · `Mathlib.Data.Nat.Choose.Basic`

The statement is `k ≤ n → n.choose k * k ! * (n - k)! = n !`. The form with a division is `Nat.choose_eq_factorial_div_factorial`. In a proof, prefer the form with products: the division `/` of $\mathbb{N}$ rounds down, and the tactics `ring` and `omega` do not reason well about it. The factorial `Nat.factorial` has the notation `n !` in the namespace `Nat`.

<?decl Nat.choose_mul_factorial_mul_factorial?>
:::

**Theorem (Sum of a row).** For each $n$, $$\sum_{k=0}^{n} \binom{n}{k} = 2^n.$$

*Proof.* Let $s$ be a finset with $n$ members. Each subset of $s$ has a card $k$ with $0 \leq k \leq n$. So the power set $\mathcal{P}(s)$ is the union of the finsets $\mathcal{P}_0(s), \ldots, \mathcal{P}_n(s)$. Two of them with $k \neq l$ do not meet, because a subset has one card. The card of a union of pairwise disjoint finsets is the sum of their cards: this follows from the card of a disjoint union of Section 1 by induction on the number of parts, and Section 3 states it in general. So $|\mathcal{P}(s)| = \sum_{k=0}^n |\mathcal{P}_k(s)|$. The left side is $2^n$ by Section 1, and the right side is $\sum_k \binom{n}{k}$ by the count of the $k$-subsets. $\square$

::: mathlib
`Finset.powerset_card_disjiUnion` · `Mathlib.Data.Finset.Powerset`

The power set as a disjoint union: `s.powerset = (range (#s + 1)).disjiUnion (fun i => powersetCard i s) _`. The numeric identity is `Nat.sum_range_choose`: `∑ m ∈ range (n + 1), n.choose m = 2 ^ n`. Mathlib proves it from the binomial theorem with $x = y = 1$.

<?decl Finset.powerset_card_disjiUnion?>
:::

**Theorem (Vandermonde).** For $m, n, k \in \mathbb{N}$, $$\binom{m+n}{k} = \sum_{j=0}^{k} \binom{m}{j} \binom{n}{k-j}.$$

*Proof.* Let $A$ and $B$ be finsets that do not meet, with $|A| = m$ and $|B| = n$. For example, $A = \{0, \ldots, m-1\}$ and $B = \{m, \ldots, m+n-1\}$. Then $|A \cup B| = m + n$, and $\mathcal{P}_k(A \cup B)$ has $\binom{m+n}{k}$ members.

Split $\mathcal{P}_k(A \cup B)$ by the number $j = |u \cap A|$, for $j = 0, \ldots, k$. The parts are pairwise disjoint and cover the finset. Fix $j$. Send $u$ to the pair $(u \cap A, u \cap B)$. Since $u \subseteq A \cup B$ and $A \cap B = \emptyset$, the finset $u$ is the disjoint union of $u \cap A$ and $u \cap B$. So $|u \cap B| = k - j$, and the pair lies in $\mathcal{P}_j(A) \times \mathcal{P}_{k-j}(B)$. The map back sends a pair $(v, w)$ to $v \cup w$. This union has $j + (k - j) = k$ members, since $v$ and $w$ do not meet, and $(v \cup w) \cap A = v$ and $(v \cup w) \cap B = w$. So the two maps are inverse, and the part for $j$ has $|\mathcal{P}_j(A)| \cdot |\mathcal{P}_{k-j}(B)| = \binom{m}{j} \binom{n}{k-j}$ members, by the product rule of Section 3. Add over $j$. $\square$

::: mathlib
`Nat.add_choose_eq` · `Mathlib.Data.Nat.Choose.Vandermonde`

Mathlib sums over the antidiagonal, the pairs $(i, j)$ with $i + j = k$, so no subtraction appears. Mathlib proves the identity with polynomials: it compares the coefficients of $X^k$ in $(1 + X)^{m+n} = (1 + X)^m (1 + X)^n$.

<?decl Nat.add_choose_eq?>
:::

### Examples

**Example (The triangle of Pascal).** The rule of Pascal computes each row from the row before it. Row $n$ lists $\binom{n}{0}, \ldots, \binom{n}{n}$.

| $n$ | row $n$ | sum |
|---|---|---|
| 0 | 1 | 1 |
| 1 | 1, 1 | 2 |
| 2 | 1, 2, 1 | 4 |
| 3 | 1, 3, 3, 1 | 8 |
| 4 | 1, 4, 6, 4, 1 | 16 |
| 5 | 1, 5, 10, 10, 5, 1 | 32 |
| 6 | 1, 6, 15, 20, 15, 6, 1 | 64 |
| 7 | 1, 7, 21, 35, 35, 21, 7, 1 | 128 |

For example $\binom{6}{3} = \binom{5}{2} + \binom{5}{3} = 10 + 10 = 20$. Each row is a palindrome, by the symmetry. The sums are the powers of $2$, by the sum of a row.

**Example (The $2$-subsets of a $5$-set).** Let $s = \{1, 2, 3, 4, 5\}$. The $2$-subsets are $$\{1,2\}, \{1,3\}, \{1,4\}, \{1,5\}, \{2,3\}, \{2,4\}, \{2,5\}, \{3,4\}, \{3,5\}, \{4,5\}.$$ There are $10 = \binom{5}{2}$. The theorem of Pascal for subsets splits them with $a = 5$: the four subsets $\{1,5\}, \{2,5\}, \{3,5\}, \{4,5\}$ contain $5$ and come from the four $1$-subsets of $\{1, 2, 3, 4\}$, and the other six are the $2$-subsets of $\{1, 2, 3, 4\}$. This is $\binom{5}{2} = \binom{4}{1} + \binom{4}{2} = 4 + 6$. Their complements are the ten $3$-subsets.

**Example (Handshakes).** In a group of $n$ people, each two shake hands once. A handshake is a $2$-subset of the group, so there are $\binom{n}{2}$ handshakes. The factorial formula gives $\binom{n}{2} = \frac{n!}{2! \, (n-2)!} = \frac{n(n-1)}{2}$ for $n \geq 2$. The formula also holds for $n = 0$ and $n = 1$, where both sides are $0$. Mathlib has it as `Nat.choose_two_right`.

**Example (A lottery).** A lottery draws $6$ numbers of $\{1, \ldots, 49\}$, and the order does not count. A ticket is a $6$-subset, so there are $$\binom{49}{6} = \frac{49 \cdot 48 \cdot 47 \cdot 46 \cdot 45 \cdot 44}{6!} = \frac{10\,068\,347\,520}{720} = 13\,983\,816$$ tickets. The first equality is the factorial formula after the cancellation of $43!$.

**Example (A committee).** A group has $6$ women and $4$ men. The committees of $3$ with at least one man are all the committees minus those with no man: $\binom{10}{3} - \binom{6}{3} = 120 - 20 = 100$. The identity of Vandermonde with $m = 4$ men, $n = 6$ women and $k = 3$ splits the same count by the number $j$ of men: $$\binom{4}{0}\binom{6}{3} + \binom{4}{1}\binom{6}{2} + \binom{4}{2}\binom{6}{1} + \binom{4}{3}\binom{6}{0} = 20 + 60 + 36 + 4 = 120.$$ The last three terms are the committees with a man, and their sum is $100$.

**Example (Squares of a row).** Put $m = n$ and $k = n$ in the identity of Vandermonde, and use the symmetry $\binom{n}{n-j} = \binom{n}{j}$. Then $$\binom{2n}{n} = \sum_{j=0}^{n} \binom{n}{j}^2.$$ For $n = 3$: $1 + 9 + 9 + 1 = 20 = \binom{6}{3}$. For $n = 4$: $1 + 16 + 36 + 16 + 1 = 70 = \binom{8}{4}$.

**Counterexample (Symmetry needs $k \leq n$).** Take $n = 2$ and $k = 3$. Then $\binom{2}{3} = 0$, because a $2$-set has no $3$-subset. In $\mathbb{N}$ the difference $2 - 3$ is $0$, so the other side is $\binom{2}{0} = 1$. Thus $\binom{n}{n-k} = \binom{n}{k}$ fails for $k > n$ in Lean, and `Nat.choose_symm` asks for `k ≤ n`. On paper, with $n - k$ negative, the right side is not defined at all.

### Common errors

- To read `powersetCard k s` as "the subsets of card at most $k$". It holds the subsets of card exactly $k$.
- To write the factorial formula with `/` in a proof. Use `Nat.choose_mul_factorial_mul_factorial`, then cancel.
- To forget the hypothesis `k ≤ n` of `Nat.choose_symm` and of the factorial formula.
- To expect `Nat.choose` to be defined by the factorial formula. The definition is the rule of Pascal, so `simp [Nat.choose]` unfolds the recursion, and `decide` computes small values.
### The library around it

Besides the power set of Section 1, the file `Mathlib.Data.Finset.Powerset` has the rules of `Finset.powersetCard`: `Finset.powersetCard_zero`, `Finset.powersetCard_self`, `Finset.powersetCard_mono`, `Finset.powersetCard_nonempty` and `Finset.powersetCard_eq_empty`, and the strict subsets `Finset.ssubsets`. The files `Mathlib.Data.Nat.Choose.*` of Volume 2 hold the numbers, for example `Nat.choose_le_middle` and `Nat.sum_Icc_choose` (Exercise 7). The reference table below lists the declarations of the module.

### Exercises

1. (A) Compute row $8$ of the triangle of Pascal from row $7$, and check that its sum is $256$.
2. (A) List the $3$-subsets of $\{a, b, c, d\}$ and match each one with its complement.
3. (A) Use the factorial formula to compute $\binom{10}{4}$. Then compute it again with $\binom{10}{4} = \frac{10 \cdot 9 \cdot 8 \cdot 7}{4!}$ and explain why the two forms agree.
4. (B) Prove $k \binom{n}{k} = n \binom{n-1}{k-1}$ for $1 \leq k \leq n$ by counting the pairs $(u, x)$ with $u$ a $k$-subset of $\{1, \ldots, n\}$ and $x \in u$ in two ways.
5. (B) Prove $\sum_{k} \binom{n}{2k} = 2^{n-1}$ for $n \geq 1$. Hint: fix $a \in s$; the map $u \mapsto u \,\triangle\, \{a\}$, which adds $a$ to $u$ or removes it, is a bijection between the subsets of even card and the subsets of odd card.
6. (B) How many paths from $(0, 0)$ to $(m, n)$ in the plane use only steps $(1, 0)$ and $(0, 1)$? Hint: a path is fixed by the set of positions of its steps $(1, 0)$ among the $m + n$ steps.
7. (B) Prove the identity of the hockey stick $\sum_{i=k}^{n} \binom{i}{k} = \binom{n+1}{k+1}$. Hint: sort the $(k+1)$-subsets of $\{0, \ldots, n\}$ by their largest member $i$.
8. (C) Prove that $\binom{n}{k} \leq \binom{n}{k+1}$ for $2k + 1 \leq n$. Hint: use the factorial formula to get $\binom{n}{k+1} (k+1) = \binom{n}{k} (n - k)$.
9. (C) Let $p$ be a prime and $0 < k < p$. Prove that $p$ divides $\binom{p}{k}$. Hint: $p$ divides $p! = \binom{p}{k} k! (p-k)!$, and $p$ divides neither $k!$ nor $(p-k)!$.

### Notes and history

The triangle of the binomial coefficients appears in the work of Pingala in India, of al-Karaji and later al-Samaw'al in the Islamic world in the tenth and twelfth centuries, and of Yang Hui in China in the thirteenth century. Pascal wrote his *Traité du triangle arithmétique* in 1654, and the name of the triangle in the West comes from it. The identity of Vandermonde is in a memoir of Alexandre-Théophile Vandermonde of 1772, and Zhu Shijie knew it in 1303. The notation $\binom{n}{k}$ is due to Andreas von Ettingshausen in 1826. The proofs by bijections of this section are standard; Stanley, *Enumerative Combinatorics*, Volume 1, Chapter 1, has many more.

In Mathlib, `Nat.choose` is in the file `Mathlib.Data.Nat.Choose.Basic`, whose authors line names Chris Hughes, Bhavik Mehta, Stuart Presnell and Antoine Chambert-Loir. The file `Mathlib.Data.Finset.Powerset` is by Mario Carneiro. The function `Finset.powersetCard` had the name `Finset.powersetLen` until 2023, when it got its present name, which says that the card is fixed. The Vandermonde file is by Johan Commelin.

### Reference

<?reference?>
