---
title: Partitions and Young diagrams
kind: theory
modules:
  - Mathlib.Combinatorics.Enumerative.Partition.Basic
  - Mathlib.Combinatorics.Enumerative.Partition.GenFun
  - Mathlib.Combinatorics.Enumerative.Partition.Glaisher
  - Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
  - Mathlib.Combinatorics.Young.YoungDiagram
  - Mathlib.Combinatorics.Young.SemistandardTableau
  - Mathlib.Combinatorics.Enumerative.Pentagonal.Basic
  - Mathlib.Combinatorics.Enumerative.Pentagonal.Ring
  - Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
  - Mathlib.Combinatorics.Enumerative.Pentagonal
  - Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
explains:
  E3: [Nat.Partition, Nat.Partition.genFun, Nat.Partition.hasProd_genFun, Nat.Partition.card_restricted_eq_card_countRestricted, Nat.Partition.card_odds_eq_card_distincts, YoungDiagram, YoungDiagram.transpose, YoungDiagram.equivPartition, Nat.Partition.conjugate, PowerSeries.WithPiTopology.tprod_one_sub_X_pow]
  E2: [Nat.Partition.parts, Nat.Partition.parts_pos, Nat.Partition.parts_sum, Nat.Partition.ofSums, Nat.Partition.ofComposition, Nat.Partition.indiscrete, Nat.Partition.restricted, Nat.Partition.countRestricted, Nat.Partition.odds, Nat.Partition.distincts, Nat.Partition.countRestricted_two, Nat.Partition.coeff_genFun, Nat.Partition.genFun_eq_tprod, Nat.Partition.powerSeriesMk_card_restricted_eq_tprod, Nat.Partition.powerSeriesMk_card_countRestricted_eq_tprod, Nat.Partition.conjugate_conjugate, YoungDiagram.transpose_transpose, YoungDiagram.rowLen, YoungDiagram.colLen, YoungDiagram.rowLen_transpose, YoungDiagram.rowLens, YoungDiagram.ofRowLens, YoungDiagram.ofPartition, YoungDiagram.toPartition, PowerSeries.pentagonalSeries, PowerSeries.coeff_pentagonalSeries_pentagonal, PowerSeries.coeff_pentagonalSeries_eq_zero, pentagonal, pentagonal_neg, pentagonal_injective, Pentagonal.tprod_one_sub_pow, SemistandardYoungTableau, SemistandardYoungTableau.highestWeight]
  E1: auto
families: []
requires: [V03.C03, V03.C06, V09.C07, V14.C07]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Partitions and Young diagrams

### Overview

A partition of $n$ is a way to write $n$ as a sum of positive integers when the order of the summands does not matter. The number $p(n)$ of partitions of $n$ grows fast: $p(10) = 42$ and $p(100) = 190569292$. No simple closed formula gives $p(n)$, but its generating function is a simple infinite product, and many identities between classes of partitions follow from identities between products.

This section defines partitions as Mathlib does, as multisets of positive integers. It proves the product formula for the generating function of partitions with conditions on the parts and on the multiplicities. From it, it proves the theorem of Glaisher, which has the theorem of Euler on odd and distinct parts as the case $m = 2$. It then draws partitions as Young diagrams, defines the conjugate partition by the transpose, and uses it to compare two more classes. It proves the pentagonal number theorem of Euler by the involution of Franklin and states the form that Mathlib proves. At the end it defines semistandard Young tableaux.

### Definitions

**Definition (partition).** Let $n \ge 0$. A *partition* of $n$ is a finite multiset $\lambda$ of positive integers with sum $n$. The elements of $\lambda$ are its *parts*. The *multiplicity* of $i$ in $\lambda$ is the number of parts equal to $i$. The number of partitions of $n$ is $p(n)$.

A partition is usually written with its parts in decreasing order, $\lambda = (\lambda_1, \lambda_2, \ldots, \lambda_r)$ with $\lambda_1 \ge \lambda_2 \ge \cdots \ge \lambda_r \ge 1$, or with exponents for the multiplicities, so that $(3, 3, 1)$ is also $3^2 1$. The empty multiset is the unique partition of $0$, so $p(0) = 1$. The partitions of $5$ are
$$5, \quad 4 + 1, \quad 3 + 2, \quad 3 + 1 + 1, \quad 2 + 2 + 1, \quad 2 + 1 + 1 + 1, \quad 1 + 1 + 1 + 1 + 1,$$
so $p(5) = 7$. The first values are

| $n$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| $p(n)$ | 1 | 1 | 2 | 3 | 5 | 7 | 11 | 15 | 22 | 30 | 42 |

A *composition* of $n$ is a sum of positive integers where the order matters. Each composition gives a partition when the order is forgotten, and each partition comes from at least one composition.

::: mathlib
`Nat.Partition` · `Mathlib.Combinatorics.Enumerative.Partition.Basic`

`Nat.Partition n` is a structure with a field `parts : Multiset ℕ` and two proofs, `parts_pos` that each part is positive and `parts_sum` that the parts add up to `n`. The type has a `Fintype` instance, so `Fintype.card (Nat.Partition n)` is $p(n)$. `Nat.Partition.ofSums n l hl` makes a partition from a multiset `l` with sum `n`, and it drops the zeros of `l`. `Nat.Partition.ofComposition` forgets the order of a composition, and `ofComposition_surj` says that each partition comes from a composition. `Nat.Partition.indiscrete n` is the partition with the single part `n`.

<?decl Nat.Partition?>
:::

**Definition (restricted partitions).** Let $P$ be a property of positive integers and let $m \ge 1$. A partition is *$P$-restricted* if each part has the property $P$. It is *$m$-count-restricted* if each part has multiplicity less than $m$. A partition is *odd* if each part is odd, and *distinct* if no part repeats, that is, if it is $2$-count-restricted.

For $n = 6$ the odd partitions are $5 + 1$, $3 + 3$, $3 + 1 + 1 + 1$ and $1 + 1 + 1 + 1 + 1 + 1$, and the distinct partitions are $6$, $5 + 1$, $4 + 2$ and $3 + 2 + 1$. There are four of each kind. This is not a chance.

::: mathlib
`Nat.Partition.restricted` · `Mathlib.Combinatorics.Enumerative.Partition.Basic`

`Nat.Partition.restricted n p` is the finset of partitions of `n` whose parts all satisfy the decidable predicate `p`. `Nat.Partition.countRestricted n m` is the finset of partitions in which each part has count less than `m`. `Nat.Partition.odds n` is `restricted n (¬ Even ·)`, and `Nat.Partition.distincts n` is the finset of partitions whose multiset of parts is `Nodup`. `countRestricted_two` says that `countRestricted n 2 = distincts n`.

<?decl Nat.Partition.restricted?>
<?decl Nat.Partition.countRestricted?>
:::

**Definition (generating function).** The *generating function* of a sequence $a_0, a_1, a_2, \ldots$ in a commutative ring $R$ is the formal power series $\sum_{n \ge 0} a_n X^n$ in $R[[X]]$.

Formal power series are defined in Volume 9, Chapter 7. To multiply infinitely many of them, give $R[[X]]$ the topology of coefficientwise convergence: a sequence of power series converges if each coefficient is eventually constant. Volume 14, Chapter 7 defines infinite products in a topological monoid. If $f_1, f_2, \ldots$ are power series with $f_i = 1 + g_i$ and the order of $g_i$ tends to infinity, then the coefficient of $X^n$ in $f_1 f_2 \cdots f_k$ stops changing when $k$ is large, and the product $\prod_{i \ge 1} f_i$ exists. For example, $\prod_{i \ge 1} (1 + X^i)$ exists, because $X^i$ has order $i$.

### Theorems and proofs

#### The product formula

Let $f(i, j)$ be a weight for each part $i \ge 1$ and each multiplicity $j \ge 1$, with values in a commutative ring $R$. The weight of a partition $\lambda$ is the product of $f(i, j_i)$ over the parts $i$ of $\lambda$, where $j_i$ is the multiplicity of $i$. The empty partition has weight $1$.

**Theorem (product formula).** In $R[[X]]$,
$$\sum_{n \ge 0} \Bigl(\sum_{\lambda \vdash n} \operatorname{wt}(\lambda)\Bigr) X^n = \prod_{i \ge 1} \Bigl(1 + \sum_{j \ge 1} f(i, j) X^{ij}\Bigr).$$

*Proof.* The factor $F_i = 1 + \sum_{j \ge 1} f(i, j) X^{ij}$ is $1$ plus a series of order at least $i$, so the product exists and its coefficient of $X^n$ equals the coefficient of $X^n$ in the finite product $F_1 F_2 \cdots F_n$. Expand this finite product. A term is a choice, for each $i \le n$, of either the $1$ of $F_i$ (call this $j_i = 0$) or the term $f(i, j_i) X^{i j_i}$ with $j_i \ge 1$. The term has degree $\sum_i i j_i$ and coefficient $\prod_{j_i \ge 1} f(i, j_i)$. The choices of degree $n$ are the families $(j_1, \ldots, j_n)$ of non-negative integers with $\sum_i i j_i = n$. Such a family is exactly the multiplicity data of a partition of $n$: the partition has $j_i$ parts equal to $i$. No part of a partition of $n$ exceeds $n$, so each partition of $n$ occurs once. The coefficient of the term is the weight of the partition. So the coefficient of $X^n$ is $\sum_{\lambda \vdash n} \operatorname{wt}(\lambda)$. $\square$

Three choices of weight give the cases of this section.

- With $f(i, j) = 1$ for all $i$ and $j$, each factor is $1 + X^i + X^{2i} + \cdots = 1/(1 - X^i)$, and
$$\sum_{n \ge 0} p(n) X^n = \prod_{i \ge 1} \frac{1}{1 - X^i}.$$
- With $f(i, j) = 1$ when $i$ has the property $P$ and $f(i, j) = 0$ otherwise, the factor is $1/(1 - X^i)$ when $P(i)$ holds and $1$ otherwise. The left side counts the $P$-restricted partitions.
- With $f(i, j) = 1$ when $j < m$ and $f(i, j) = 0$ otherwise, the factor is $1 + X^i + \cdots + X^{(m-1)i}$. The left side counts the $m$-count-restricted partitions.

::: mathlib
`Nat.Partition.genFun` · `Mathlib.Combinatorics.Enumerative.Partition.GenFun`

`Nat.Partition.genFun f` is the power series with coefficient `∑ p : n.Partition, p.parts.toFinsupp.prod f` at `n`, and `coeff_genFun` restates this. The function `f : ℕ → ℕ → R` takes the part first and the multiplicity second. `hasProd_genFun` is the product formula with shifted indices: the factor at `i` is `1 + ∑' j, f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1))`. The ring `R` is a commutative semiring with a topology, and the product is taken in the topology `PowerSeries.WithPiTopology` on `R⟦X⟧`. It is a scoped instance, so the file opens `PowerSeries.WithPiTopology` first. The topology on `R` does not matter for the result: with the discrete topology, convergence is coefficientwise eventual constancy, as above. The module docstring lists the case $f = 1$, the generating function of $p(n)$ itself, as a TODO.

<?decl Nat.Partition.genFun?>
<?decl Nat.Partition.hasProd_genFun?>
:::

The two specialisations have their own names: `powerSeriesMk_card_restricted_eq_tprod` gives the product $\prod_i (\text{if } P(i+1) \text{ then } \sum_j X^{(i+1)j} \text{ else } 1)$, and `powerSeriesMk_card_countRestricted_eq_tprod` gives $\prod_i \sum_{j < m} X^{(i+1)j}$ for $m > 0$.

#### The theorem of Glaisher

**Theorem (Glaisher).** Let $m \ge 1$ and $n \ge 0$. The number of partitions of $n$ in which no part is divisible by $m$ equals the number of partitions of $n$ in which each part has multiplicity less than $m$.

*Proof by generating functions.* Work in $\mathbb{Z}[[X]]$. By the product formula, the two generating functions are
$$A = \prod_{m \nmid i} \frac{1}{1 - X^i}, \qquad B = \prod_{i \ge 1} \bigl(1 + X^i + \cdots + X^{(m-1)i}\bigr) = \prod_{i \ge 1} \frac{1 - X^{mi}}{1 - X^i}.$$
The second form of $B$ uses $(1 - X^i)(1 + X^i + \cdots + X^{(m-1)i}) = 1 - X^{mi}$, and $1 - X^i$ is a unit of $\mathbb{Z}[[X]]$. Let $D = \prod_{i \ge 1} (1 - X^i)^{-1}$ and $E = \prod_{i \ge 1} (1 - X^{mi})$. Both products exist, and the product of two convergent products is the product of the termwise products, so $B = E D$. Split $D$ by the divisibility of $i$ by $m$: $D = A \cdot \prod_{k \ge 1} (1 - X^{mk})^{-1} = A E^{-1}$. So $B = E \cdot A E^{-1} = A$. Equal power series have equal coefficients. $\square$

*Proof by a bijection.* Each positive integer $a$ has a unique form $a = r m^k$ with $k \ge 0$ and $m \nmid r$. Let $\lambda$ have no part divisible by $m$, and let $r$ have multiplicity $c_r$ in $\lambda$. Write $c_r$ in base $m$, $c_r = \sum_k d_{r,k} m^k$ with digits $0 \le d_{r,k} < m$. Replace the $c_r$ parts equal to $r$ by $d_{r,k}$ parts equal to $r m^k$ for each $k$. The sum does not change, because $\sum_k d_{r,k} \cdot r m^k = r c_r$. The part $r m^k$ occurs $d_{r,k} < m$ times, and different pairs $(r, k)$ give different parts. So the result $\mu$ has all multiplicities less than $m$. Conversely, from $\mu$ with all multiplicities less than $m$, write each part as $r m^k$ and break each part $r m^k$ into $m^k$ parts equal to $r$. Uniqueness of base-$m$ digits shows that the two maps are inverse. $\square$

The case $m = 2$ is the theorem of Euler.

**Corollary (Euler).** The number of partitions of $n$ into odd parts equals the number of partitions of $n$ into distinct parts.

For $n = 6$, the bijection sends $3 + 3$ to $6$, sends $3 + 1 + 1 + 1$ (with $c_1 = 3 = 1 + 2$) to $3 + 2 + 1$, sends $1^6$ (with $c_1 = 6 = 2 + 4$) to $4 + 2$, and fixes $5 + 1$.

::: mathlib
`Nat.Partition.card_restricted_eq_card_countRestricted` · `Mathlib.Combinatorics.Enumerative.Partition.Glaisher`

The statement is `#(restricted n (¬ m ∣ ·)) = #(countRestricted n m)` for `0 < m`. The proof compares the two power series in `ℤ⟦X⟧` with `powerSeriesMk_card_restricted_eq_powerSeriesMk_card_countRestricted` and reads off the coefficient of `X ^ n`. It is the first proof above.

<?decl Nat.Partition.card_restricted_eq_card_countRestricted?>
:::

::: mathlib
`Nat.Partition.card_odds_eq_card_distincts` · `Mathlib.Combinatorics.Enumerative.Partition.Glaisher`

`#(odds n) = #(distincts n)`. It follows from the theorem of Glaisher with `m = 2`, from `countRestricted_two`, and from the fact that a natural number is not even exactly when `2` does not divide it.

<?decl Nat.Partition.card_odds_eq_card_distincts?>
:::

#### Young diagrams and conjugation

**Definition (Young diagram).** A *Young diagram* is a finite set $\mu$ of cells $(i, j) \in \mathbb{N} \times \mathbb{N}$ such that $(i, j) \in \mu$, $i' \le i$ and $j' \le j$ imply $(i', j') \in \mu$. The cell $(i, j)$ is in row $i$ and column $j$. Rows go down and columns go to the right. The *length* of row $i$ is the number of cells in row $i$, and the length of column $j$ is the number of cells in column $j$.

In the product order on $\mathbb{N} \times \mathbb{N}$, a Young diagram is a finite lower set. The row lengths of a Young diagram decrease weakly, because $(i, j) \in \mu$ implies $(i - 1, j) \in \mu$. The non-zero row lengths are a partition of the number of cells. Conversely, a partition $\lambda_1 \ge \cdots \ge \lambda_r$ gives the diagram $\{(i, j) : i < r, j < \lambda_{i+1}\}$. The two maps are inverse, so Young diagrams with $n$ cells correspond to partitions of $n$. The diagram of $(5, 3, 3, 1)$ is
$$\begin{array}{lllll} \square & \square & \square & \square & \square \\ \square & \square & \square \\ \square & \square & \square \\ \square \end{array}$$

::: mathlib
`YoungDiagram` · `Mathlib.Combinatorics.Young.YoungDiagram`

A `YoungDiagram` is a structure with `cells : Finset (ℕ × ℕ)` and a proof `isLowerSet` that the coercion of `cells` to a set is a lower set. It is a `SetLike` type, so `(i, j) ∈ μ` makes sense. Young diagrams form a distributive lattice under inclusion with `⊥` the empty diagram. `YoungDiagram.rowLen μ i` and `YoungDiagram.colLen μ j` are the lengths, `YoungDiagram.rowLens μ` is the list of non-zero row lengths, and `rowLens_sorted` says that it is weakly decreasing. `YoungDiagram.ofRowLens` builds a diagram from a weakly decreasing list.

<?decl YoungDiagram?>
:::

::: mathlib
`YoungDiagram.equivPartition` · `Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram`

`YoungDiagram.equivPartition : { μ : YoungDiagram // μ.card = n } ≃ Nat.Partition n`. Its two directions are `YoungDiagram.toPartition`, which takes the row lengths, and `YoungDiagram.ofPartition`, which sorts the parts into decreasing order and builds the rows. `rowLens_ofPartition_eq_sort_parts` records the sort.

<?decl YoungDiagram.equivPartition?>
:::

**Definition (transpose and conjugate).** The *transpose* of a Young diagram $\mu$ is $\mu^t = \{(j, i) : (i, j) \in \mu\}$. The *conjugate* $\lambda'$ of a partition $\lambda$ is the partition of the transpose of its diagram.

The transpose is again a lower set, and $(\mu^t)^t = \mu$. Row $i$ of $\mu^t$ is column $i$ of $\mu$, so the parts of $\lambda'$ are the column lengths of the diagram of $\lambda$: $\lambda'_j$ is the number of parts of $\lambda$ that are at least $j$. The conjugate of $(5, 3, 3, 1)$ is $(4, 3, 3, 1, 1)$.

::: mathlib
`YoungDiagram.transpose` · `Mathlib.Combinatorics.Young.YoungDiagram`

`YoungDiagram.transpose μ` has the cells `(Equiv.prodComm _ _).finsetCongr μ.cells`, the image of the cells under the swap, and `mem_transpose` says `c ∈ μ.transpose ↔ c.swap ∈ μ`. `transpose_transpose` is the involution, `card_transpose` keeps the number of cells, and `rowLen_transpose` says that `μ.transpose.rowLen i = μ.colLen i`. `transposeOrderIso` packs the transpose as an order isomorphism.

<?decl YoungDiagram.transpose?>
:::

::: mathlib
`Nat.Partition.conjugate` · `Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram`

`Nat.Partition.conjugate p` is `(YoungDiagram.ofPartition p).transpose.toPartition`, with the proof that the transpose has `n` cells. `conjugate_conjugate` says that conjugation is an involution, so it is a bijection of `Nat.Partition n` to itself.

<?decl Nat.Partition.conjugate?>
:::

**Theorem.** Let $n, k \ge 0$. The number of partitions of $n$ with at most $k$ parts equals the number of partitions of $n$ with all parts at most $k$.

*Proof.* The number of parts of $\lambda$ is the length of the first column of its diagram, and the largest part is the length of the first row. The transpose exchanges the first row and the first column. So conjugation maps the partitions with at most $k$ parts onto the partitions with largest part at most $k$. Conjugation is an involution, so this map is a bijection. $\square$

With the product formula, the second count has the generating function $\prod_{i = 1}^{k} (1 - X^i)^{-1}$, so this product is also the generating function of partitions with at most $k$ parts.

#### The pentagonal number theorem

For an integer $k$, the *pentagonal number* is $\omega(k) = k(3k - 1)/2$. For $k = 1, -1, 2, -2, 3, -3$ it takes the values $1, 2, 5, 7, 12, 15$. The map $\omega$ is injective on $\mathbb{Z}$, and its values are non-negative integers.

**Theorem (Euler).** In $\mathbb{Z}[[X]]$,
$$\prod_{n \ge 1} (1 - X^n) = \sum_{k \in \mathbb{Z}} (-1)^k X^{k(3k-1)/2} = 1 - X - X^2 + X^5 + X^7 - X^{12} - X^{15} + \cdots.$$

*Proof.* Apply the product formula with $f(i, 1) = -1$ and $f(i, j) = 0$ for $j \ge 2$. Then each factor is $1 - X^i$, and the coefficient of $X^n$ on the left is $e(n) - o(n)$, where $e(n)$ and $o(n)$ are the numbers of distinct partitions of $n$ with an even and with an odd number of parts. So it is sufficient to find, for each $n$, a map on distinct partitions of $n$ that changes the number of parts by one and that is an involution, except on at most one partition.

Let $\lambda = (\lambda_1 > \lambda_2 > \cdots > \lambda_r)$ be a distinct partition with $r \ge 1$. Let $s = \lambda_r$ be its smallest part. Let $\sigma$ be the length of the *slope* of $\lambda$: the largest $\sigma \le r$ such that $\lambda_i = \lambda_1 - i + 1$ for $i \le \sigma$. In the diagram, the slope is the run of cells at the right ends of the first $\sigma$ rows. Define the two moves:

- *Move A*, when $s \le \sigma$: remove the smallest part and add $1$ to each of the $s$ largest parts.
- *Move B*, when $s > \sigma$: subtract $1$ from each of the $\sigma$ largest parts and add a new smallest part $\sigma$.

Both moves keep the sum. Move A removes one part and move B adds one, so each move changes the parity of the number of parts.

First suppose $\sigma < r$, so the slope does not contain the smallest part. If $s \le \sigma$, move A adds $1$ to $\lambda_1, \ldots, \lambda_s$, all in the slope. The new parts are $\lambda_1 + 1 > \cdots > \lambda_s + 1$, then $\lambda_{s+1}, \ldots, \lambda_{r-1}$. These are distinct, because $\lambda_s + 1 > \lambda_s > \lambda_{s+1}$. In the result, each part is greater than $s$, because each part is at least $\lambda_{r-1} > \lambda_r = s$. The slope of the result has length exactly $s$, because it starts with $\lambda_1 + 1, \ldots, \lambda_s + 1$ and the next part is at most $\lambda_{s+1} < \lambda_s = (\lambda_s + 1) - 1$. So move B applies to the result. It subtracts $1$ from the $s$ largest parts and adds the part $s$, which restores $\lambda$. (If the result has only $s$ parts, its smallest part is $\lambda_s + 1 \ge s + 2$, so it is not one of the exceptions below.) If $s > \sigma$, move B subtracts $1$ from the slope. The parts $\lambda_1 - 1 > \cdots > \lambda_\sigma - 1$ stay larger than $\lambda_{\sigma+1}$, because $\lambda_{\sigma + 1} < \lambda_\sigma - 1$ by the maximality of $\sigma$. The new smallest part $\sigma$ is less than $s$. In the result, the smallest part is $\sigma$, and the slope has length at least $\sigma$. So move A applies and restores $\lambda$.

Now suppose $\sigma = r$, so $\lambda = (s + r - 1, \ldots, s + 1, s)$. Move A needs $s \le r - 1$ when the smallest part is removed, because only $r - 1$ parts remain to receive the $s$ units. Move B produces the new part $r$, and it must be less than the old smallest part decreased by one, $s - 1$. So the moves work and are inverse unless $s = r$ or $s = r + 1$. These two exceptions are the partitions
$$(2r - 1, \ldots, r + 1, r) \text{ of } \frac{r(3r - 1)}{2} = \omega(r), \qquad (2r, \ldots, r + 2, r + 1) \text{ of } \frac{r(3r + 1)}{2} = \omega(-r).$$
The empty partition is a third exception, of $0 = \omega(0)$, with $0$ parts.

So for each $n$, the moves pair the distinct partitions of $n$ with opposite signs, except one partition with $r$ parts when $n = \omega(\pm r)$ and none otherwise. The coefficient of $X^n$ is $(-1)^r$ when $n = \omega(r)$ or $n = \omega(-r)$, and $0$ when $n$ is not a pentagonal number. Since $(-1)^{-r} = (-1)^r$, this is the coefficient of the right side. $\square$

**Example (the recursion of Euler for $p(n)$).** Multiply the pentagonal number theorem by $\sum_n p(n) X^n = \prod_i (1 - X^i)^{-1}$. The product is $1$, so for $n \ge 1$,
$$p(n) = p(n - 1) + p(n - 2) - p(n - 5) - p(n - 7) + p(n - 12) + p(n - 15) - \cdots,$$
with $p(m) = 0$ for $m < 0$. For example, $p(7) = p(6) + p(5) - p(2) - p(0) = 11 + 7 - 2 - 1 = 15$, and $p(10) = p(9) + p(8) - p(5) - p(3) = 30 + 22 - 7 - 3 = 42$. This recursion computes $p(n)$ with about $\sqrt{n}$ terms for each $n$.

::: mathlib
`PowerSeries.WithPiTopology.tprod_one_sub_X_pow` · `Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries`

`∏' n, (1 - X ^ (n + 1) : R⟦X⟧) = pentagonalSeries R` for a commutative ring `R` with a Hausdorff topology. `PowerSeries.pentagonalSeries R` is the series whose coefficient at `n` is `Int.negOnePow k` when `n = pentagonal k` and `0` otherwise, and `coeff_pentagonalSeries_pentagonal` and `coeff_pentagonalSeries_eq_zero` restate this. The function `pentagonal : ℤ → ℕ` is `(k * (3 * k - 1) / 2).toNat`, and `pentagonal_injective` justifies the definition. The proof does not use the involution of Franklin. It comes from `Pentagonal.tprod_one_sub_pow` in `Mathlib.Combinatorics.Enumerative.Pentagonal.Ring`, a telescoping argument with the auxiliary series $A_k = \sum_n X^{(k+1)n} \prod_{i \le n} (1 - X^{k+i+1})$ and the recursion $A_k = 1 - X^{2k+3} - X^{3k+5} A_{k+1}$. `Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction` proves the same identity for $\|x\| < 1$ in a complete normed ring.

<?decl PowerSeries.WithPiTopology.tprod_one_sub_X_pow?>
:::

#### Semistandard Young tableaux

**Definition (semistandard Young tableau).** Let $\mu$ be a Young diagram. A *semistandard Young tableau* of shape $\mu$ is a map $T$ from the cells of $\mu$ to $\mathbb{N}$ such that the entries increase weakly along each row from left to right and increase strictly down each column.

For each shape there is the tableau whose row $i$ contains only the value $i$. Its columns increase strictly because row $i$ lies above row $i + 1$. One semistandard tableau of shape $(4, 2, 1)$ is
$$\begin{array}{llll} 0 & 0 & 0 & 2 \\ 1 & 1 \\ 2 \end{array}$$
Semistandard tableaux are the starting point of the combinatorics of symmetric functions: the Schur polynomial of shape $\mu$ is the sum over the tableaux of the monomials $x^T = \prod_{c} x_{T(c)}$.

::: mathlib
`SemistandardYoungTableau` · `Mathlib.Combinatorics.Young.SemistandardTableau`

`SemistandardYoungTableau μ` is a structure with a function `entry : ℕ → ℕ → ℕ` and three proofs: `row_weak'`, `col_strict'`, and `zeros'`, which says that the entry is `0` outside `μ`. The value outside `μ` is fixed so that two tableaux with the same entries on `μ` are equal. There is a `FunLike` instance, so `T i j` is the entry. `SemistandardYoungTableau.highestWeight μ` is the tableau with `i` in row `i`.

<?decl SemistandardYoungTableau?>
:::

### Examples

**Example (Glaisher for $m = 3$ and $n = 6$).** The partitions of $6$ with no part divisible by $3$ are $5 + 1$, $4 + 2$, $4 + 1 + 1$, $2 + 2 + 2$, $2 + 2 + 1 + 1$, $2 + 1^4$ and $1^6$. There are seven. The partitions of $6$ in which no part repeats three times or more are $6$, $5 + 1$, $4 + 2$, $4 + 1 + 1$, $3 + 3$, $3 + 2 + 1$ and $2 + 2 + 1 + 1$. There are also seven. The bijection sends $2 + 2 + 2$ (with $c_2 = 3 = 0 + 1 \cdot 3$) to $6$, and $1^6$ (with $c_1 = 6 = 0 + 2 \cdot 3$) to $3 + 3$.

**Example (self-conjugate partitions).** A partition is self-conjugate if $\lambda' = \lambda$. The self-conjugate partitions of $8$ are $(4, 2, 1, 1)$ and $(3, 3, 2)$. Cut the diagram of a self-conjugate partition into hooks along the diagonal: the hook at $(i, i)$ is the cells $(i, j)$ with $j \ge i$ and $(j, i)$ with $j > i$. Each hook has odd size, and the sizes decrease strictly. For $(4, 2, 1, 1)$ the sizes are $7, 1$, and for $(3, 3, 2)$ they are $5, 3$. Exercise 6 makes this a bijection.

**Example (the coefficient check).** The coefficient of $X^5$ in $\prod_n (1 - X^n)$ is $+1$. The distinct partitions of $5$ are $5$, $4 + 1$ and $3 + 2$: one with an odd number of parts and two with an even number, so $e(5) - o(5) = 1$. The moves of Franklin pair $5$ with $4 + 1$: the partition $5$ has $s = 5 > \sigma = 1$, so move B gives $4 + 1$. The partition $3 + 2$ has $s = 2 = \sigma = r$. It is the exception $(2r - 1, \ldots, r)$ with $r = 2$, and $\omega(2) = 5$. Its sign is $(-1)^2 = +1$.

### The library around it

Mathlib proves the product formula in general and the theorems of Glaisher and Euler, defines Young diagrams and their transpose, and proves the pentagonal number theorem. The index of this edition has no declaration for the generating function $\prod_i (1 - X^i)^{-1}$ of $p(n)$ itself, which the docstring of `Mathlib.Combinatorics.Enumerative.Partition.GenFun` lists as a TODO, and so no declaration for the recursion of Euler for $p(n)$. It also has no declaration for the asymptotic formula of Hardy and Ramanujan, the congruences of Ramanujan, the hook length formula, the Robinson-Schensted-Knuth correspondence or Schur polynomials.

`Mathlib.Combinatorics.Enumerative.Partition.Basic` has more maps than this section uses. `Nat.Partition.ofSym` turns a point of `Sym σ n` into the partition of $n$ given by its multiplicities, and `Nat.Partition.toFinsuppAntidiag` sends a partition to the finitely supported function of its counts.

The module `Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction` evaluates the pentagonal number theorem at a point. For $x$ in a complete normed commutative ring with $\|x\| < 1$, for example $\mathbb{C}$, the function `eulerFunction x` is the value of the pentagonal power series at $x$ (`eulerFunction_def`). It equals the infinite product $\prod_{n \geq 0} (1 - x^{n + 1})$ (`eulerFunction_eq_tprod`, and `hasProd_eulerFunction` in the form with `HasProd`), and it equals the sum $\sum_{k \in \mathbb{Z}} (-1)^k x^{k(3k - 1)/2}$ (`eulerFunction_eq_tsum_pentagonal`, and `hasSum_eulerFunction_pentagonal` with `HasSum`). Together these two results are the analytic form of the theorem. The module `Mathlib.Combinatorics.Enumerative.Pentagonal` has no declarations of its own and only imports the other pentagonal modules.

Common errors of a learner:

- `Nat.Partition.ofSums` drops the zeros of the multiset. `(ofSums n l hl).parts` is `l.filter (· ≠ 0)`, not `l`.
- The function `f` in `Nat.Partition.genFun f` takes the part first and the multiplicity second. Its values at part `0` or at multiplicity `0` are not used.
- The product in `hasProd_genFun` needs the scoped topology `PowerSeries.WithPiTopology`. Without `open scoped PowerSeries.WithPiTopology`, the instance search does not find a topology on `R⟦X⟧`.
- Mathlib uses matrix coordinates for Young diagrams: `(i, j)` is row `i` and column `j`, with rows counted downward. It is not the Cartesian convention of the French notation.
- `pentagonal` takes an integer and returns a natural number. `pentagonal (-k)` is $k(3k + 1)/2$, by `pentagonal_neg`.

### Exercises

1. (A) List the $15$ partitions of $7$ and check the recursion $p(7) = p(6) + p(5) - p(2) - p(0)$.
2. (A) Compute the conjugate of $(6, 4, 4, 2, 1)$ and check that conjugating twice gives the partition back.
3. (A) List the odd partitions and the distinct partitions of $7$, and apply the bijection of Glaisher with $m = 2$ to each odd partition.
4. (B) Show that the number of partitions of $n$ into exactly $k$ parts equals the number of partitions of $n - k$ into at most $k$ parts. Hint: subtract $1$ from each part.
5. (B) Show that the number of partitions of $n$ into at most $k$ parts, each at most $l$, is the coefficient of $X^n$ in a polynomial of degree $kl$, and that this polynomial is symmetric: its coefficients at $n$ and $kl - n$ are equal. Hint: take the complement of the diagram in the $k \times l$ rectangle.
6. (B) Show that the number of self-conjugate partitions of $n$ equals the number of partitions of $n$ into distinct odd parts. Hint: use the diagonal hooks of the examples.
7. (B) Prove that the transpose of a Young diagram is a Young diagram and that the row lengths of the transpose are the column lengths of the diagram.
8. (C) Prove that $\prod_{i \ge 1} (1 + X^{2i - 1}) = \sum_{n \ge 0} c(n) X^n$, where $c(n)$ is the number of self-conjugate partitions of $n$, and compute $c(n)$ for $n \le 10$.
9. (C) Show that the involution of Franklin, applied to the distinct partitions of $12$, leaves exactly one fixed point, and identify it.

### Notes and history

Euler proved the theorem on odd and distinct parts in 1748 in the *Introductio in analysin infinitorum*, by the same comparison of products as in this section. He found the pentagonal number theorem by computation and published a proof in 1750. Glaisher gave his generalisation in 1883. The involution is due to Franklin, in 1881, and it was one of the first bijective proofs of an identity of power series. Young diagrams carry the name of Alfred Young, who used them from 1900 in the representation theory of the symmetric groups. The books of Andrews (*The theory of partitions*) and of Stanley (*Enumerative combinatorics*, Volume 2, for tableaux) are standard references. The Authors line of the Mathlib files names Bhavik Mehta for the partition basics, Weiyi Wang for the generating functions, the theorem of Glaisher and the pentagonal number theorem, Kevin Gomez for the link between partitions and Young diagrams, and Jake Levinson for Young diagrams and tableaux.

### Reference

<?reference?>
