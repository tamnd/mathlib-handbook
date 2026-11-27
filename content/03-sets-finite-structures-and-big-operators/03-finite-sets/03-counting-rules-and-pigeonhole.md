---
title: The rules of counting and the pigeonhole principle
kind: theory
modules:
  - Mathlib.Data.Finset.Prod
  - Mathlib.Data.Finset.Union
explains:
  E3: [Finset.exists_ne_map_eq_of_card_lt_of_maps_to, Finset.card_product]
  E2: [Finset.product, Finset.biUnion, Finset.card_union_of_disjoint, Finset.card_sdiff, Finset.card_inter_add_card_sdiff, Finset.card_le_card_of_injOn, Finset.card_nbij]
  E1: auto
families: []
requires: [V03.C02, V04]
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

## The rules of counting and the pigeonhole principle

### Overview

Most counting arguments use a few rules. The rule of sum adds the cards of finsets that do not meet. The rules of difference, product and bijection give the cards of $t \setminus s$ and $s \times t$, and of two finsets in bijection. Inclusion and exclusion corrects the rule of sum when the finsets meet. The pigeonhole principle says that a map from a larger finset to a smaller one is not injective.

This section proves these rules from Section 1 and uses them on numbers, on intervals of $\mathbb{N}$ and on the classical problems of the pigeonhole principle. Inclusion and exclusion for any number of finsets and double counting need sums, so they are in Section 3 of Chapter 6.

### Definitions

**Definition (Disjoint).** Two finsets $s$ and $t$ are disjoint when $s \cap t = \emptyset$, that is, when no element is in both. A family $(t_i)_{i \in I}$ of finsets is pairwise disjoint when $t_i$ and $t_j$ are disjoint for all $i \neq j$ in $I$.

**Definition (Union of a family).** Let $I$ be a finset and let $t_i$ be a finset of $\beta$ for each $i \in I$. The union $\bigcup_{i \in I} t_i$ is the finset of the elements that lie in some $t_i$ with $i \in I$.

::: mathlib
`Finset.biUnion` · `Mathlib.Data.Finset.Union`

`s.biUnion t` is the union of the finsets `t i` for `i ∈ s`. It needs `DecidableEq β`, because it removes repetitions; the variant `Finset.disjiUnion` takes a proof of pairwise disjointness instead. The membership rule is `Finset.mem_biUnion`. Disjointness is the predicate `Disjoint s t` of Volume 4, and `Finset.disjoint_left` states it with members.

<?decl Finset.biUnion?>
:::

**Definition (Product).** The product of a finset $s$ of $\alpha$ and a finset $t$ of $\beta$ is the finset $s \times t = \{(a, b) : a \in s,\ b \in t\}$ of the type $\alpha \times \beta$.

::: mathlib
`Finset.product` · `Mathlib.Data.Finset.Prod`

The notation is `s ×ˢ t`, with a small `s` above the cross. The membership rule is `Finset.mem_product`: `p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t`. The product needs no decidable equality, because no repetition can appear.

<?decl Finset.product?>
:::

**Definition (Interval).** For $a, b \in \mathbb{N}$, the interval $[a, b]$ is the finset $\{n \in \mathbb{N} : a \leq n \leq b\}$. It is empty when $b < a$.

Mathlib writes `Finset.Icc a b`. The letters say which ends are closed: `Ico a b` is $\{a \leq n < b\}$, `Ioc` and `Ioo` are the other two. The intervals exist in each locally finite order. Volume 4 defines them, and this section only counts them in $\mathbb{N}$.

### Theorems and proofs

**Theorem (Rule of sum).** If $s$ and $t$ are disjoint, then $|s \cup t| = |s| + |t|$. More generally, if $(t_i)_{i \in I}$ is pairwise disjoint, then $$\Bigl|\bigcup_{i \in I} t_i\Bigr| = \sum_{i \in I} |t_i|.$$

*Proof.* The case of two finsets is the card of a disjoint union of Section 1. For a family, use induction on $I$. If $I = \emptyset$, both sides are $0$. Let $j \notin I$ and assume the claim for $I$. The union over $I \cup \{j\}$ is $U \cup t_j$ with $U = \bigcup_{i \in I} t_i$. The finsets $U$ and $t_j$ are disjoint: an element of $U$ lies in some $t_i$ with $i \in I$, so $i \neq j$, and $t_i \cap t_j = \emptyset$. By the case of two finsets and the hypothesis of induction, $|U \cup t_j| = \sum_{i \in I} |t_i| + |t_j|$, which is the sum over $I \cup \{j\}$. $\square$

::: mathlib
`Finset.card_union_of_disjoint` · `Mathlib.Data.Finset.Card`

The hypothesis is `Disjoint s t`. The equivalence `Finset.card_union_eq_card_add_card` says that the equality holds only for disjoint finsets. For a family, the lemma is `Finset.card_biUnion` in `Mathlib.Algebra.BigOperators.Group.Finset.Basic`: the hypothesis is `(s : Set ι).PairwiseDisjoint t` and the conclusion is a sum `∑ u ∈ s, #(t u)`. Sums over finsets are the subject of Chapter 6.

<?decl Finset.card_union_of_disjoint?>
:::

**Theorem (Rule of difference).** For finsets $s$ and $t$, $|s \cap t| + |t \setminus s| = |t|$. So $|t \setminus s| = |t| - |s \cap t|$, and $|t \setminus s| = |t| - |s|$ when $s \subseteq t$.

*Proof.* Each member of $t$ is in $s$ or not in $s$. So $t$ is the union of $s \cap t$ and $t \setminus s$, and these two finsets are disjoint. The rule of sum gives $|t| = |s \cap t| + |t \setminus s|$. When $s \subseteq t$, $s \cap t = s$. $\square$

::: mathlib
`Finset.card_inter_add_card_sdiff` · `Mathlib.Data.Finset.Card`

The additive form, `#(s ∩ t) + #(s \ t) = #s`, with the roles of the letters as in the lemma. It has no subtraction, so `omega` uses it with no side condition.

<?decl Finset.card_inter_add_card_sdiff?>
:::

::: mathlib
`Finset.card_sdiff` · `Mathlib.Data.Finset.Card`

The form with subtraction: `#(t \ s) = #t - #(s ∩ t)`. It needs no hypothesis, because $|s \cap t| \leq |t|$, so the truncated subtraction of $\mathbb{N}$ gives the true value.

<?decl Finset.card_sdiff?>
:::

**Theorem (Rule of bijection).** Let $f : \alpha \to \beta$ map $s$ into $t$. If $f$ is injective on $s$, then $|s| \leq |t|$. If $f$ is also onto $t$, then $|s| = |t|$.

*Proof.* The image $f(s)$ is a subset of $t$, because $f$ maps $s$ into $t$. By the card of an image of Section 1, $|f(s)| = |s|$. By the card of a subset, $|s| = |f(s)| \leq |t|$. If $f$ is onto $t$, then $f(s) = t$, and $|s| = |t|$. $\square$

::: mathlib
`Finset.card_le_card_of_injOn` · `Mathlib.Data.Finset.Card`

The hypotheses are `Set.MapsTo f s t` and `Set.InjOn f s`, both about the sets that the finsets give by coercion. The function `f` is a function on all of `α`; only its values on `s` count.

<?decl Finset.card_le_card_of_injOn?>
:::

::: mathlib
`Finset.card_nbij` · `Mathlib.Data.Finset.Card`

The three hypotheses `Set.MapsTo i s t`, `Set.InjOn i s` and `Set.SurjOn i s t` give `#s = #t`. The variant `Finset.card_nbij'` takes an inverse map in place of injectivity and surjectivity, and is often the easiest to use.

<?decl Finset.card_nbij?>
:::

**Theorem (Rule of product).** For finsets $s$ and $t$, $|s \times t| = |s| \cdot |t|$.

*Proof.* For $a \in s$, put $R_a = \{(a, b) : b \in t\}$, the row of $a$. The map $b \mapsto (a, b)$ is injective and maps $t$ onto $R_a$, so $|R_a| = |t|$ by the rule of bijection. The rows for $a \neq a'$ are disjoint, because their pairs have different first entries. Each pair $(a, b) \in s \times t$ lies in the row $R_a$. So $s \times t = \bigcup_{a \in s} R_a$, a pairwise disjoint union. By the rule of sum, $|s \times t| = \sum_{a \in s} |t| = |s| \cdot |t|$. $\square$

::: mathlib
`Finset.card_product` · `Mathlib.Data.Finset.Prod`

The statement is `#(s ×ˢ t) = #s * #t`, with no hypothesis. The analogue for finite types is `Fintype.card_prod` of Chapter 4.

<?decl Finset.card_product?>
:::

**Theorem (Inclusion and exclusion for three finsets).** For finsets $A$, $B$ and $C$, $$|A \cup B \cup C| = |A| + |B| + |C| - |A \cap B| - |A \cap C| - |B \cap C| + |A \cap B \cap C|.$$

*Proof.* Read the cards as integers, so that the subtractions are those of $\mathbb{Z}$. Section 1 gives the rule $|X \cup Y| = |X| + |Y| - |X \cap Y|$ for any two finsets. Apply it to $X = A \cup B$ and $Y = C$: $$|A \cup B \cup C| = |A \cup B| + |C| - |(A \cup B) \cap C|.$$ The first term is $|A| + |B| - |A \cap B|$, by the rule again. For the third term, the law of distribution gives $(A \cup B) \cap C = (A \cap C) \cup (B \cap C)$, and $(A \cap C) \cap (B \cap C) = A \cap B \cap C$. By the rule once more, $$|(A \cup B) \cap C| = |A \cap C| + |B \cap C| - |A \cap B \cap C|.$$ Put the two results into the first equation. The signs give the claim. $\square$

Chapter 6 proves the general form for $n$ finsets by sums.

**Theorem (Card of an interval).** For $a, b \in \mathbb{N}$ with $a \leq b + 1$, $|[a, b]| = b + 1 - a$. For $d \geq 1$, the number of multiples of $d$ in $[1, n]$ is $\lfloor n / d \rfloor$.

*Proof.* Put $m = b + 1 - a$. The map $i \mapsto a + i$ sends $\operatorname{range} m = \{0, \ldots, m - 1\}$ into $[a, b]$, because $a \leq a + i \leq a + m - 1 = b$. It is injective. It is onto $[a, b]$: for $a \leq n \leq b$, the number $i = n - a$ satisfies $0 \leq i \leq b - a < m$. By the rule of bijection, $|[a, b]| = |\operatorname{range} m| = m$.

For the second claim, put $q = \lfloor n / d \rfloor$, so $qd \leq n < (q + 1) d$. The map $j \mapsto dj$ sends $[1, q]$ into the multiples of $d$ in $[1, n]$, because $d \leq dj \leq dq \leq n$. It is injective, since $d \neq 0$. It is onto: a multiple $dj$ with $1 \leq dj \leq n$ has $j \geq 1$ and $j \leq n/d$, so $j \leq q$. By the first claim $|[1, q]| = q$. $\square$

::: mathlib
`Nat.card_Icc` · `Mathlib.Order.Interval.Finset.Nat`

The statement is `#(Icc a b) = b + 1 - a` for all `a b : ℕ`, with no hypothesis. When $b + 1 < a$ the interval is empty, and the truncated subtraction gives $0$, which is correct. The companions `Nat.card_Ico` and `Nat.card_Ioc` give $b - a$, and `Int.card_Icc` gives `(b + 1 - a).toNat` for integers. The file is in Volume 4.

<?decl Nat.card_Icc?>
:::

**Theorem (Pigeonhole principle).** Let $f : \alpha \to \beta$ map the finset $s$ into the finset $t$. If $|t| < |s|$, then there are $x, y \in s$ with $x \neq y$ and $f(x) = f(y)$.

*Proof.* Assume the contrary: for all $x, y \in s$, $f(x) = f(y)$ implies $x = y$. Then $f$ is injective on $s$. By the rule of bijection, $|s| \leq |t|$. This contradicts $|t| < |s|$. $\square$

::: mathlib
`Finset.exists_ne_map_eq_of_card_lt_of_maps_to` · `Mathlib.Data.Finset.Card`

The hypotheses are `#t < #s` and `Set.MapsTo f s t`. The version for finite types is `Fintype.exists_ne_map_eq_of_card_lt` of Chapter 4. Mathlib proves it as above, by contradiction with `Finset.card_le_card_of_injOn`.

<?decl Finset.exists_ne_map_eq_of_card_lt_of_maps_to?>
:::

**Theorem (Strong pigeonhole principle).** Let $f$ map $s$ into $t$, and let $k \in \mathbb{N}$. If $|s| > k \, |t|$, then some $y \in t$ has a fibre $F_y = \{x \in s : f(x) = y\}$ with more than $k$ members.

*Proof.* Each $x \in s$ lies in the fibre $F_{f(x)}$, and $f(x) \in t$. Two fibres $F_y$ and $F_{y'}$ with $y \neq y'$ are disjoint, because $f(x)$ has one value. So $s = \bigcup_{y \in t} F_y$ is a pairwise disjoint union, and the rule of sum gives $|s| = \sum_{y \in t} |F_y|$. If each fibre had at most $k$ members, the sum would be at most $k \, |t|$, which contradicts $|s| > k \, |t|$. $\square$

For $k = 1$ this is the pigeonhole principle: a fibre with two members gives $x \neq y$ with $f(x) = f(y)$.

::: mathlib
`Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to` · `Mathlib.Combinatorics.Pigeonhole`

The hypotheses are `∀ a ∈ s, f a ∈ t` and `#t * n < #s`. The file has variants with `≤`, with weights and for finite types, and belongs to the volume on combinatorics. The decomposition into fibres is `Finset.card_eq_sum_card_fiberwise` of Chapter 6.

<?decl Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to?>
:::

### Examples

**Example (Divisible by 2, 3 or 5).** Let $A$, $B$ and $C$ be the multiples of $2$, $3$ and $5$ in $[1, 100]$. A number is a multiple of $2$ and $3$ exactly when it is a multiple of $6$, because $2$ and $3$ are coprime. In the same way $A \cap C$, $B \cap C$ and $A \cap B \cap C$ are the multiples of $10$, $15$ and $30$. The card of an interval gives $$|A| = 50,\ |B| = 33,\ |C| = 20,\ |A \cap B| = 16,\ |A \cap C| = 10,\ |B \cap C| = 6,\ |A \cap B \cap C| = 3.$$ Inclusion and exclusion gives $$|A \cup B \cup C| = 50 + 33 + 20 - 16 - 10 - 6 + 3 = 74.$$ So $100 - 74 = 26$ numbers in $[1, 100]$ have none of the factors $2$, $3$ and $5$. A check: in each block of $30$ consecutive numbers there are $\varphi(30) = 8$ numbers prime to $30$, so $[1, 90]$ has $24$. In $[91, 100]$ the numbers prime to $30$ are $91$ and $97$. The total is $26$.

**Example (Birthdays).** In any group of $13$ people, two have their birthday in the same month. The map that sends a person to the month of the birthday goes from a finset of $13$ members to a finset of $12$ members. The pigeonhole principle gives two different people with the same month. With $25$ people, $25 > 2 \cdot 12$, so the strong form gives a month with at least $3$ birthdays.

**Example (Consecutive numbers).** Choose $n + 1$ numbers of $[1, 2n]$. Then two of them are consecutive, so they are coprime. Proof: put the numbers of $[1, 2n]$ in the $n$ boxes $\{1, 2\}, \{3, 4\}, \ldots, \{2n - 1, 2n\}$. The map that sends $x$ to the box of $x$ goes from $n + 1$ chosen numbers to $n$ boxes. Two different numbers are in one box, so they are $2i - 1$ and $2i$. Two consecutive numbers are coprime, because a common factor divides their difference $1$. The $n$ odd numbers show that $n$ numbers do not suffice.

**Example (A divisor among $n + 1$ numbers).** Choose $n + 1$ numbers of $[1, 2n]$. Then one of them divides another. Proof: write each chosen $x$ as $x = 2^a m$ with $m$ odd. The odd part $m$ lies in $\{1, 3, \ldots, 2n - 1\}$, a finset with $n$ members. By the pigeonhole principle two different chosen numbers $x = 2^a m$ and $y = 2^b m$ have the same odd part. Since $x \neq y$, $a \neq b$. If $a < b$, then $x$ divides $y$. If $b < a$, then $y$ divides $x$. For $n = 5$, the choice $\{6, 7, 8, 9, 10, 4\}$ has the pair $4$ and $8$ with odd part $1$.

**Example (A block with sum divisible by $n$).** Let $a_1, \ldots, a_n$ be integers. Then some block $a_{i+1} + \cdots + a_j$ with $0 \leq i < j \leq n$ has a sum divisible by $n$. Proof: put $S_0 = 0$ and $S_j = a_1 + \cdots + a_j$. The $n + 1$ indices $0, \ldots, n$ map to the $n$ residues modulo $n$ by $j \mapsto S_j \bmod n$. By the pigeonhole principle two indices $i < j$ have $S_i \equiv S_j \pmod n$. Then $n$ divides $S_j - S_i = a_{i+1} + \cdots + a_j$. For $n = 4$ and $(3, 5, 6, 1)$: the sums are $0, 3, 8, 14, 15$, with residues $0, 3, 0, 2, 3$. The indices $0$ and $2$ give the block $3 + 5 = 8$.

**Counterexample (Pigeonhole needs $|t| < |s|$).** For $s = t = [1, n]$ and $f$ the identity, $f$ maps $s$ into $t$ and is injective. So the hypothesis $|t| < |s|$ can not be weakened to $|t| \leq |s|$. The strong form fails in the same way for $|s| = k \, |t|$: the map $[1, 12] \to [1, 4]$, $x \mapsto \lceil x / 3 \rceil$, has fibres with exactly $3$ members each.

### Common errors

- To use the rule of sum for finsets that meet. Check disjointness first, or use inclusion and exclusion.
- To write inclusion and exclusion with subtraction in $\mathbb{N}$ and then add in a different order. In $\mathbb{N}$, $5 - 7 + 3 = 3$, not $1$. Move the cards to $\mathbb{Z}$, or use the additive forms.
- To count $[a, b]$ as $b - a$ members. It has $b - a + 1$. The half-open `Finset.Ico a b` has $b - a$.
- To apply the pigeonhole principle with a map that does not land in $t$. The hypothesis `Set.MapsTo f s t` must be proved, for example that each residue modulo $n$ is less than $n$.
- To confuse `s ×ˢ t`, a finset of pairs, with `s ∩ t`.

### The library around it

The pattern of names is `Finset.card_<op>`: `Finset.card_product`, `Finset.card_sdiff`, `Finset.card_disjUnion`, `Finset.card_sigma`. The comparisons through maps are `Finset.card_le_card_of_injOn`, `Finset.card_le_card_of_surjOn`, `Finset.card_nbij` and `Finset.card_bij`. `Mathlib.Data.Finset.Prod` also has the diagonal `Finset.diag` and `Finset.offDiag`. The reference table below lists the declarations of the modules.

### Exercises

1. (A) How many numbers in $[1, 1000]$ are multiples of $3$ or of $7$?
2. (A) Compute $|[17, 63]|$, $|\{n : 17 \leq n < 63\}|$ and $|[63, 17]|$.
3. (A) Show that among any $5$ points with integer coordinates in the plane, two have a midpoint with integer coordinates. Hint: sort the points by the parities of their coordinates.
4. (B) How many numbers in $[1, 1000]$ are not divisible by $2$, $3$, $5$ or $7$? Use inclusion and exclusion for four finsets, which has $15$ terms.
5. (B) Prove that $|A \cup B \cup C| \geq |A| + |B| + |C| - |A \cap B| - |A \cap C| - |B \cap C|$.
6. (B) In a group of $n \geq 2$ people, each person knows some of the others, and knowing is symmetric. Prove that two people know the same number of others. Hint: the numbers lie in $\{0, \ldots, n - 1\}$, and $0$ and $n - 1$ can not both occur.
7. (C) Prove the theorem of Erdős and Szekeres: each sequence of $n^2 + 1$ different real numbers has a monotone subsequence of length $n + 1$. Hint: attach to each term the length of the longest increasing subsequence that starts at it, and use the strong pigeonhole principle.
8. (C) Let $s$ be a subset of $[1, 100]$ with $51$ members. Prove that $s$ contains two numbers whose sum is $101$, and that $51$ can not be replaced by $50$.

### Notes and history

The rules of sum and product are the base of combinatorics and have no single author. The pigeonhole principle is named after Dirichlet, who used it in 1834 under the name *Schubfachprinzip*, the principle of drawers, for his theorem on rational approximation. It appears earlier in a book of Jean Leurechon of 1622. The method of inclusion and exclusion appears in the work of de Moivre on probability (1718), and Sylvester gave the general form in 1883. The theorem of Exercise 7 is due to Erdős and Szekeres (1935).

In Mathlib, the basic pigeonhole lemma is part of `Mathlib.Data.Finset.Card`, whose authors line names Leonardo de Moura and Jeremy Avigad. The strong forms with fibres and weights are in `Mathlib.Combinatorics.Pigeonhole`, by Kyle Miller and Yury Kudryashov. In the names `Finset.card_nbij` and `Finset.card_bij`, the letter `n` marks the form whose map takes no proof of membership.

### Reference

<?reference?>
