---
title: Catalan numbers and Dyck words
kind: theory
modules:
  - Mathlib.Combinatorics.Enumerative.Catalan.Basic
  - Mathlib.Combinatorics.Enumerative.Catalan.Tree
  - Mathlib.Combinatorics.Enumerative.DyckWord
  - Mathlib.Combinatorics.Enumerative.Schroder
explains:
  E3: [catalan, catalan_succ, catalan_eq_centralBinom_div, succ_mul_catalan_eq_centralBinom, DyckWord, DyckWord.firstReturn, DyckWord.nest_insidePart_add_outsidePart, DyckWord.equivTree, DyckWord.card_dyckWord_semilength_eq_catalan, BinaryTree.treesOfNumNodesEq, BinaryTree.treesOfNumNodesEq_card_eq_catalan, Nat.largeSchroder]
  E2: [catalan_zero, catalan_one, catalan_two, catalan_three, catalan_succ', DyckWord.semilength, DyckWord.nest, DyckWord.insidePart, DyckWord.outsidePart, DyckWord.count_D_le_count_U, DyckWord.count_D_lt_count_U_of_lt_firstReturn, DyckWord.semilength_insidePart_add_semilength_outsidePart_add_one, DyckWord.firstReturn_add, DyckWord.toTree, DyckWord.ofTree, DyckWord.numNodes_toTree, DyckWord.equivTreesOfNumNodesEq, DyckWord.infix_of_le, BinaryTree.mem_treesOfNumNodesEq, BinaryTree.treesOfNumNodesEq_succ, BinaryTree.pairwiseNode, Nat.largeSchroder_succ, Nat.smallSchroder, Nat.smallSchroder_succ, Nat.smallSchroder_succ_eq_largeSchroder_div_two, Nat.two_mul_smallSchroder_succ, Nat.even_largeSchroder]
  E1: auto
families: []
requires: [V03.C03, V03.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Catalan numbers and Dyck words

### Overview

The Catalan numbers $1, 1, 2, 5, 14, 42, \ldots$ count many families of objects: balanced strings of brackets, binary trees, triangulations of a convex polygon, and more. Each family has a decomposition that gives the same recursion $C_{n+1} = \sum_{i=0}^{n} C_i C_{n-i}$. The closed form is $C_n = \binom{2n}{n}/(n+1)$.

Mathlib defines the Catalan numbers by the recursion. It proves the closed form by a telescoping sum. It defines Dyck words, which are balanced bracket strings, and binary trees with a given number of nodes, and it proves that both are counted by the Catalan numbers. This section follows that path. It proves the closed form a second time by the reflection argument, which explains the number $\binom{2n}{n} - \binom{2n}{n-1}$. At the end it gives the Schröder numbers, which Mathlib defines by recursion only.

### Definitions

**Definition (Catalan numbers).** The *Catalan numbers* are $C_0 = 1$ and $C_{n+1} = \sum_{i=0}^{n} C_i\, C_{n-i}$.

The first values are as follows.

| $n$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| $C_n$ | 1 | 1 | 2 | 5 | 14 | 42 | 132 | 429 | 1430 | 4862 | 16796 |

For example $C_4 = C_0 C_3 + C_1 C_2 + C_2 C_1 + C_3 C_0 = 5 + 2 + 2 + 5 = 14$.

::: mathlib
`catalan` · `Mathlib.Combinatorics.Enumerative.Catalan.Basic`

`catalan : ℕ → ℕ` is defined with the sum over `i : Fin n.succ`, and `catalan_succ` restates it. `catalan_succ'` writes the sum over `antidiagonal n`, the pairs $(i, j)$ with $i + j = n$. This form fits the decompositions of this section. The values `catalan_zero` to `catalan_three` are simp lemmas or are proved by the closed form.

<?decl catalan?>
:::

**Definition (Dyck word).** A *Dyck word* is a finite word in the letters $U$ and $D$ with as many $U$ as $D$, such that each prefix has at least as many $U$ as $D$. Its *semilength* is half its length.

Read $U$ as an opening bracket and $D$ as a closing bracket: the Dyck words are the balanced bracket strings. Read $U$ as a step $(1, 1)$ and $D$ as a step $(1, -1)$: the Dyck words are the lattice paths from $(0, 0)$ to $(2n, 0)$ that do not go below the horizontal axis. The *height* of a prefix is its number of $U$ minus its number of $D$. The Dyck words of semilength $3$ are $$UUUDDD, \quad UUDUDD, \quad UUDDUD, \quad UDUUDD, \quad UDUDUD.$$

::: mathlib
`DyckWord` · `Mathlib.Combinatorics.Enumerative.DyckWord`

A `DyckWord` is a structure with a list `toList : List DyckStep` and two proofs: the counts of `U` and `D` are equal, and `DyckWord.count_D_le_count_U` for every prefix `take i`. The type `DyckStep` has the two constructors `U` and `D`. Dyck words form an additive monoid under concatenation, with `0` the empty word. `DyckWord.semilength` is the count of `D`.

<?decl DyckWord?>
:::

**Definition (First return).** Let $w$ be a nonempty Dyck word. Its *first return* is the least index $k$ such that the prefix of length $k + 1$ has height $0$.

Such an index exists, since $w$ itself has height $0$. In the path picture, $k$ is the step at which the path first comes back to the axis.

### Theorems and proofs

**Lemma (First return decomposition).** Each nonempty Dyck word $w$ has a unique form $w = U p D q$ with Dyck words $p$ and $q$. The semilengths satisfy $|p| + |q| + 1 = |w|$, where $|\cdot|$ is the semilength.

*Proof.* Let $k$ be the first return of $w$. The prefix of length $1$ has height $\ge 0$, so $w$ begins with $U$, and its height is $1$. By the choice of $k$, the prefixes of length $1, \ldots, k$ have height $\ge 1$, and the prefix of length $k + 1$ has height $0$. So letter $k$ is $D$. Let $p$ be the letters $1, \ldots, k - 1$ and $q$ the letters after $k$. A prefix of $p$ of length $j$ has height equal to the height of the prefix of $w$ of length $j + 1$ minus $1$, which is $\ge 0$, and $p$ as a whole has height $0$. So $p$ is a Dyck word. The word $q$ starts at height $0$ and its prefixes have the heights of the longer prefixes of $w$, so $q$ is a Dyck word. The count of $D$ gives the semilength formula.

For uniqueness, let $w = U p D q$ with $p, q$ Dyck words. Inside $U p$ every prefix has height $\ge 1$, since the prefixes of $p$ have height $\ge 0$. The prefix $U p D$ has height $0$. So the first return of $w$ is the position of this $D$, and $p$ and $q$ are fixed by $w$. $\square$

::: mathlib
`DyckWord.nest_insidePart_add_outsidePart` · `Mathlib.Combinatorics.Enumerative.DyckWord`

`DyckWord.nest p` is the word $U p D$, and `DyckWord.insidePart` and `DyckWord.outsidePart` are the words $p$ and $q$ of the lemma. Both are `0` on the empty word. The lemma is `p ≠ 0 → p.insidePart.nest + p.outsidePart = p`, and the semilengths are `DyckWord.semilength_insidePart_add_semilength_outsidePart_add_one`. `DyckWord.count_D_lt_count_U_of_lt_firstReturn` is the height bound used in the proof.

<?decl DyckWord.nest_insidePart_add_outsidePart?>
:::

::: mathlib
`DyckWord.firstReturn` · `Mathlib.Combinatorics.Enumerative.DyckWord`

The definition uses `List.findIdx` on `range p.toList.length`: it is the first `i` with equal counts of `U` and `D` in `take (i + 1)`. On the empty word it is `0`. `DyckWord.firstReturn_add` computes it on a concatenation.

<?decl DyckWord.firstReturn?>
:::

**Theorem (Dyck words are counted by Catalan numbers).** There are $C_n$ Dyck words of semilength $n$.

*Proof.* Let $d_n$ be the number of Dyck words of semilength $n$. The empty word is the only one of semilength $0$, so $d_0 = 1$. By the lemma, $w \mapsto (p, q)$ is a bijection from the Dyck words of semilength $n + 1$ onto the pairs of Dyck words with semilengths $(i, n - i)$, $0 \le i \le n$. The inverse is $(p, q) \mapsto U p D q$. So $d_{n+1} = \sum_{i=0}^{n} d_i\, d_{n-i}$. This is the recursion of $C_n$ with the same start, so $d_n = C_n$ by strong induction. $\square$

The same decomposition gives a bijection with binary trees. A binary tree is either empty or a node with a left and a right subtree. Send the empty word to the empty tree, and $U p D q$ to the node whose left subtree is the tree of $p$ and whose right subtree is the tree of $q$. The number of nodes is the semilength. So there are $C_n$ binary trees with $n$ nodes. For example $UUDDUD = U(UD)D(UD)$ goes to a root with two children, and $UDUDUD = U()D(UDUD)$ goes to a path of three nodes that always turns right.

::: mathlib
`DyckWord.equivTree` · `Mathlib.Combinatorics.Enumerative.DyckWord`

The equivalence `DyckWord ≃ BinaryTree Unit` has the maps `DyckWord.toTree` and `DyckWord.ofTree` described above. `BinaryTree` lives in `Mathlib.Data.Tree.Basic`, and `BinaryTree Unit` is a tree with no labels. `DyckWord.numNodes_toTree` says that `numNodes` is the semilength, and `DyckWord.equivTreesOfNumNodesEq n` restricts the equivalence to the words of semilength `n`.

<?decl DyckWord.equivTree?>
:::

::: mathlib
`BinaryTree.treesOfNumNodesEq` · `Mathlib.Combinatorics.Enumerative.Catalan.Tree`

`treesOfNumNodesEq n : Finset (BinaryTree Unit)` is the finset of trees with `n` nodes, built by recursion with `BinaryTree.pairwiseNode`, which forms all nodes from a finset of left and a finset of right subtrees. `BinaryTree.treesOfNumNodesEq_succ` is the recursion over `antidiagonal n`, and `BinaryTree.mem_treesOfNumNodesEq` says what the members are.

<?decl BinaryTree.treesOfNumNodesEq?>
:::

::: mathlib
`DyckWord.card_dyckWord_semilength_eq_catalan` · `Mathlib.Combinatorics.Enumerative.DyckWord`

The statement is `Fintype.card { p // p.semilength = n } = catalan n`. Mathlib proves it through the trees: `BinaryTree.treesOfNumNodesEq_card_eq_catalan` counts the trees by the recursion, as in the proof above, and the equivalence transfers the count.

<?decl DyckWord.card_dyckWord_semilength_eq_catalan?>
<?decl BinaryTree.treesOfNumNodesEq_card_eq_catalan?>
:::

**Theorem (Closed form).** $C_n = \binom{2n}{n} - \binom{2n}{n-1} = \dfrac{1}{n+1}\dbinom{2n}{n}$ for $n \ge 0$, with $\binom{2n}{-1} = 0$.

*Proof.* By the previous theorem it is enough to count Dyck words. A word with $n$ letters $U$ and $n$ letters $D$ is a path from $(0, 0)$ to $(2n, 0)$, and there are $\binom{2n}{n}$ of them. Call a path *bad* when it reaches height $-1$. Reflect a bad path after the first step $t$ at which it reaches height $-1$: change every $U$ after step $t$ into $D$ and every $D$ into $U$. The new path ends at height $-1 - 1 = -2$, so it has $n - 1$ letters $U$ and $n + 1$ letters $D$. Every path with these letter counts reaches height $-1$, and reflecting it after its first visit to $-1$ gives back a bad path. The two reflections are inverse, since they use the same step $t$. So there are $\binom{2n}{n-1}$ bad paths, and $$C_n = \binom{2n}{n} - \binom{2n}{n-1} = \binom{2n}{n}\left(1 - \frac{n}{n+1}\right) = \frac{1}{n+1}\binom{2n}{n}.$$ The middle step uses $\binom{2n}{n-1} = \binom{2n}{n} \cdot \frac{n}{n+1}$. $\square$

::: mathlib
`catalan_eq_centralBinom_div` · `Mathlib.Combinatorics.Enumerative.Catalan.Basic`

The statement is `catalan n = n.centralBinom / (n + 1)` with natural division, where `Nat.centralBinom n` is $\binom{2n}{n}$. The proof is not the reflection. It works in `ℚ` with the helper $G(n, j) = \binom{2j}{j}\binom{2(n-j)}{n-j}(2j - n)/(2n(n+1))$, for which $G(n+1, i+1) - G(n+1, i) = \frac{1}{i+1}\binom{2i}{i} \cdot \frac{1}{n-i+1}\binom{2(n-i)}{n-i}$. By strong induction the recursion becomes a telescoping sum, and its value is $G(n+1, n+1) - G(n+1, 0) = \binom{2n+2}{n+1}/(n+2)$. This is a trick of Gosper.

<?decl catalan_eq_centralBinom_div?>
:::

::: mathlib
`succ_mul_catalan_eq_centralBinom` · `Mathlib.Combinatorics.Enumerative.Catalan.Basic`

The form without division: `(n + 1) * catalan n = n.centralBinom`. It is the more useful form for rewriting, since it has no natural division.

<?decl succ_mul_catalan_eq_centralBinom?>
:::

**Definition (Schröder numbers).** The *large Schröder numbers* are $L_0 = 1$ and $L_{n+1} = L_n + \sum_{i=0}^{n} L_i L_{n-i}$. The *small Schröder numbers* are $s_0 = 1$ and $s_n = L_n / 2$ for $n \ge 1$.

$L_n$ counts the lattice paths from $(0, 0)$ to $(n, n)$ with steps $(1, 0)$, $(0, 1)$ and $(1, 1)$ that never go above the diagonal. A path starts with a diagonal step, which gives the term $L_n$, or it is a decomposition like the first return, which gives the sum. The values are $L_n = 1, 2, 6, 22, 90, 394$ for $n = 0, \ldots, 5$, and $s_n = 1, 1, 3, 11, 45, 197$.

::: mathlib
`Nat.largeSchroder` · `Mathlib.Combinatorics.Enumerative.Schroder`

`Nat.largeSchroder` is defined by the recursion, with `Nat.largeSchroder_succ`. `Nat.even_largeSchroder` says that $L_n$ is even for $n \ne 0$, so the division in `Nat.smallSchroder` is exact. Mind the index: `Nat.smallSchroder_succ_eq_largeSchroder_div_two` is `n ≠ 0 → (n + 1).smallSchroder = n.largeSchroder / 2`, and `Nat.two_mul_smallSchroder_succ` is the same without division. So Mathlib's $s_{n+1}$ is $L_n / 2$, which is the small Schröder number of the usual sequence shifted by one. `Nat.smallSchroder_succ` is a recursion for the small numbers alone. The index of this edition has no declaration that the Schröder numbers count paths.

<?decl Nat.largeSchroder?>
:::

### Examples

**Example (A check of the closed form).** For $n = 10$, $\binom{20}{10} = 184756 = 11 \cdot 16796$, so $C_{10} = 16796$, as in the table. The reflection form gives $\binom{20}{10} - \binom{20}{9} = 184756 - 167960 = 16796$.

**Example (Decompositions for $n = 3$).** The five Dyck words of semilength $3$ split by the semilength $i$ of $p$:

- $i = 0$: $UD\,UUDD$ and $UD\,UDUD$, with $q$ of semilength $2$, two words;
- $i = 1$: $U(UD)D\,UD$, one word;
- $i = 2$: $U(UUDD)D$ and $U(UDUD)D$, two words.

This is $5 = C_0 C_2 + C_1 C_1 + C_2 C_0 = 2 + 1 + 2$.

**Example (Bad paths for $n = 2$).** The six words with two $U$ and two $D$ are $UUDD$, $UDUD$, $UDDU$, $DUUD$, $DUDU$, $DDUU$. The last four are bad. Their reflections are $UDDD$, $DDDU$, $DDUD$, $DUDD$, the four words with one $U$ and three $D$. So $C_2 = 6 - 4 = 2$.

### The library around it

The Catalan files prove two counts, for Dyck words and for binary trees. The TODO of `Mathlib.Combinatorics.Enumerative.Catalan.Basic` asks for more: the index of this edition has no declaration that the Catalan numbers count triangulations of polygons, noncrossing partitions or permutations that avoid a pattern. Dyck words also carry a partial order: `p ≤ q` holds when `p` is reached from `q` by taking inside and outside parts, and `DyckWord.infix_of_le` says that `p` is then an infix of `q`. This order is used for well-founded recursion on Dyck words.

Common errors of a learner:

- `catalan_eq_centralBinom_div` uses natural division. To move it into `ℚ` or to divide both sides, use `succ_mul_catalan_eq_centralBinom` and `Nat.succ_dvd_centralBinom`.
- A `DyckWord` is not a `List DyckStep`. The list is `p.toList`, and there is a coercion to lists.
- `Nat.smallSchroder (n + 1)` is $L_n / 2$, not $L_{n+1} / 2$.

### Exercises

1. (A) Compute $C_5$ from the recursion and from the closed form.
2. (A) List the binary trees with three nodes and the Dyck word of each one under the bijection of this section.
3. (A) Show that $C_n$ is odd when $n = 2^k - 1$ for some $k$, by checking $n = 0, 1, 3, 7$ in the table. Hint: this is only a check of the table.
4. (B) Show that the number of sequences $0 \le a_1 \le a_2 \le \cdots \le a_n$ of integers with $a_i \le i - 1$ is $C_n$. Hint: read a Dyck word and record the height before each $D$.
5. (B) Prove $\binom{2n}{n-1} = \frac{n}{n+1}\binom{2n}{n}$ from the factorial formula of Volume 3, Chapter 3.
6. (B) Show that the number of Dyck words of semilength $n$ that touch the axis only at the two ends is $C_{n-1}$ for $n \ge 1$.
7. (C) Show that $C_n$ counts the triangulations of a convex polygon with $n + 2$ vertices. Hint: the triangle on the edge from vertex $0$ to vertex $n + 1$ has a third vertex $i + 1$, and it splits the polygon in two.
8. (C) Check the recursion of the large Schröder numbers for $L_3 = 22$ by listing the paths from $(0, 0)$ to $(2, 2)$ and counting the paths to $(3, 3)$ by their first return to the diagonal.

### Notes and history

The numbers carry the name of Eugène Catalan, who studied them in 1838, but they appear earlier in the work of Euler and Segner on triangulations of polygons. The reflection argument is commonly credited to André (1887), although his own argument was different. Schröder studied his numbers in 1870 in a problem on bracketings. The Authors line of the Mathlib files names Julian Kuelshammer for the Catalan files, Jeremy Tan for Dyck words and Weijie Jiang for the Schröder numbers.

### Reference

<?reference?>
