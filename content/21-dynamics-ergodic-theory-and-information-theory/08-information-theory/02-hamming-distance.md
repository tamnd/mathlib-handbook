---
title: The Hamming distance
kind: theory
modules:
  - Mathlib.InformationTheory.Hamming
explains:
  E3: [hammingDist, hammingNorm, Hamming, hammingDist_triangle, hammingDist_eq_hammingNorm]
  E2: [hammingDist_eq_zero, hammingDist_comm, hammingDist_le_card_fintype, hammingDist_comp_le_hammingDist, hammingDist_comp, hammingDist_smul, hammingNorm_eq_zero, Hamming.toHamming, Hamming.ofHamming, Hamming.dist_eq_hammingDist, Hamming.norm_eq_hammingNorm, Hamming.instMetricSpace, Hamming.instNormedAddCommGroupOfAddCommGroup, Hamming.instDiscreteTopology, Hamming.instModule]
  E1: auto
families: []
requires: [V03, V07, V13.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Hamming distance

### Overview

A channel with noise changes some letters of a transmitted word. The number of changed letters is the Hamming distance between the sent word and the received word. An error correcting code is a set of words that are far apart in this distance, so that a few errors still leave the sent word recognisable. This section defines the Hamming distance and the Hamming weight, proves that they give a metric and a norm, and explains the type synonym `Hamming` that carries them in Mathlib. It then proves on paper the basic facts of coding theory: the minimum distance controls error detection and correction, the minimum distance of a linear code is its minimum weight, and the Hamming bound holds. The example is the Hamming code of length $7$.

### Definitions

Let $\iota$ be a finite set of $n$ positions and $(\beta_i)_{i \in \iota}$ a family of sets. A word is an element $x \in \prod_i \beta_i$. Most often $\beta_i = A$ for one alphabet $A$, and the words are the elements of $A^n$.

**Definition (Hamming distance).** The *Hamming distance* of two words is
$$d(x, y) = \#\{i \in \iota : x_i \neq y_i\}.$$

**Definition (Hamming weight).** If each $\beta_i$ has a zero, the *Hamming weight* or *Hamming norm* of $x$ is $\mathrm{wt}(x) = \#\{i : x_i \neq 0\} = d(x, 0)$.

::: mathlib
`hammingDist` · `Mathlib.InformationTheory.Hamming`

`hammingDist x y : ℕ` is `#{i | x i ≠ y i}` for `x y : (i : ι) → β i`, with `[Fintype ι]` and `[(i : ι) → DecidableEq (β i)]`. The weight is `hammingNorm x = #{i | x i ≠ 0}`. Both are natural numbers, not real numbers. The basic lemmas are `hammingDist_comm`, `hammingDist_eq_zero` (distance $0$ if and only if equal), `hammingDist_le_card_fintype` (at most $n$) and `hammingNorm_eq_zero`.

<?decl hammingDist?>
:::

**Definition (Code and minimum distance).** A *code* of length $n$ over $A$ is a set $C \subseteq A^n$ with at least two words. Its *minimum distance* is $d(C) = \min\{d(x, y) : x, y \in C, x \neq y\}$. If $A$ is a finite field $\mathbb{F}_q$ and $C$ is a subspace, then $C$ is a *linear code*, of type $[n, k, d]$ when $\dim C = k$ and $d(C) = d$.

### Theorems and proofs

**Theorem (Hamming metric).** The Hamming distance is a metric: $d(x, y) = 0$ if and only if $x = y$, $d(x, y) = d(y, x)$, and $d(x, z) \le d(x, y) + d(y, z)$.

*Proof.* The first two claims are clear. If $x_i \neq z_i$, then $x_i \neq y_i$ or $y_i \neq z_i$. So $\{i : x_i \neq z_i\} \subseteq \{i : x_i \neq y_i\} \cup \{i : y_i \neq z_i\}$, and the cardinality of a union is at most the sum of the cardinalities. $\square$

::: mathlib
`hammingDist_triangle` · `Mathlib.InformationTheory.Hamming`

`hammingDist x z ≤ hammingDist x y + hammingDist y z`, in `ℕ`. The variants `hammingDist_triangle_left` and `hammingDist_triangle_right` permute the arguments, as for `dist_triangle_left`.

<?decl hammingDist_triangle?>
:::

**Proposition (Maps on the letters).** Let $f_i : \gamma_i \to \beta_i$ and $f(x) = (f_i(x_i))_i$. Then $d(f(x), f(y)) \le d(x, y)$, with equality if each $f_i$ is injective. If each $\beta_i$ is a group, then $d(x, y) = \mathrm{wt}(-x + y)$.

*Proof.* If $f_i(x_i) \neq f_i(y_i)$, then $x_i \neq y_i$; for injective $f_i$ the converse holds. In a group, $x_i \neq y_i$ if and only if $-x_i + y_i \neq 0$. $\square$

In particular, multiplication by a nonzero scalar of a field does not change the distance.

::: mathlib
`hammingDist_eq_hammingNorm` · `Mathlib.InformationTheory.Hamming`

For `[(i : ι) → AddGroup (β i)]`: `hammingDist x y = hammingNorm (-x + y)`. The order $-x + y$ makes the lemma true in noncommutative groups. The maps on letters are `hammingDist_comp_le_hammingDist` and `hammingDist_comp`, with the hypothesis `∀ i, Function.Injective (f i)`. For scalars, `hammingDist_smul` asks that `k` be `IsSMulRegular` on each `β i`.

<?decl hammingDist_eq_hammingNorm?>
:::

The product $\prod_i \beta_i$ already has a metric in Mathlib when each $\beta_i$ is a metric space: the sup metric of Volume 13, Chapter 3. A second metric instance on the same type would conflict with it. So Mathlib puts the Hamming metric on a type synonym.

::: mathlib
`Hamming` · `Mathlib.InformationTheory.Hamming`

`Hamming β` is a copy of `(i : ι) → β i`. The equivalences `Hamming.toHamming` and `Hamming.ofHamming` move between the two types. On `Hamming β` there are the instances `MetricSpace` with `Hamming.dist_eq_hammingDist`, `DiscreteTopology`, `NormedAddCommGroup` for commutative groups with `Hamming.norm_eq_hammingNorm`, and `Module`. The distance of `Hamming β` is real valued, the cast of the natural number `hammingDist`.

<?decl Hamming?>
:::

The topology is discrete because distinct words have distance at least $1$.

**Theorem (Detection and correction).** Let $C$ be a code with $d(C) \ge d$ and let $t = \lfloor (d - 1)/2 \rfloor$.

1. If a codeword $c$ suffers between $1$ and $d - 1$ errors, the received word is not a codeword. So the code detects $d - 1$ errors.
2. The balls $B(c, t) = \{y : d(y, c) \le t\}$ for $c \in C$ are pairwise disjoint. So a word received with at most $t$ errors has a unique nearest codeword, the sent word. The code corrects $t$ errors.

*Proof.* (1) The received word $y$ has $1 \le d(y, c) \le d - 1$, so $y \neq c$, and $y \notin C$ because distinct codewords have distance at least $d$. (2) If $y \in B(c, t) \cap B(c', t)$, then $d(c, c') \le 2t \le d - 1$, so $c = c'$. Let $y$ be received from $c$ with at most $t$ errors. Each other codeword $c'$ has $d(y, c') \ge d(c, c') - d(y, c) \ge d - t > t$. $\square$

**Proposition (Linear codes).** For a linear code $C \neq 0$, $d(C)$ is the least weight of a nonzero codeword.

*Proof.* For $x \neq y$ in $C$, $d(x, y) = \mathrm{wt}(y - x)$ and $y - x$ is a nonzero codeword. Conversely $\mathrm{wt}(c) = d(c, 0)$ and $0 \in C$. $\square$

**Theorem (Hamming bound).** If $C \subseteq A^n$, $|A| = q$, corrects $t$ errors in the sense of part 2, then
$$|C| \sum_{j = 0}^{t} \binom{n}{j} (q - 1)^j \le q^n.$$

*Proof.* A word at distance exactly $j$ from $c$ is given by a set of $j$ positions and a different letter at each, so the ball $B(c, t)$ has $\sum_{j \le t} \binom{n}{j}(q-1)^j$ elements. The balls are disjoint subsets of $A^n$. $\square$

A code with equality in the Hamming bound is *perfect*. The index of this edition has no declaration for codes, minimum distance or these bounds; they are on paper.

### Examples

**Example (The Hamming code of length 7).** Let $H$ be the $3 \times 7$ matrix over $\mathbb{F}_2$ whose columns $h_1, \ldots, h_7$ are the seven nonzero vectors of $\mathbb{F}_2^3$. It has rank $3$, so $C = \ker H$ has dimension $4$ and $16$ codewords. A word of weight $1$ has $H e_i = h_i \neq 0$, and a word of weight $2$ has $H(e_i + e_j) = h_i + h_j \neq 0$ since the columns are distinct. So $C$ has no nonzero word of weight below $3$. The columns $001$, $010$ and $011$ sum to $0$, which gives a codeword of weight $3$. Thus $C$ is a $[7, 4, 3]$ code and corrects one error. To decode $y = c + e_i$, compute the syndrome $H y = h_i$; it names the wrong position. The code is perfect: $16 \cdot (1 + 7) = 128 = 2^7$.

**Example (The repetition code).** The code $\{000, 111\} \subseteq \mathbb{F}_2^3$ has $d = 3$ and corrects one error by a majority vote. It is perfect too: $2 \cdot (1 + 3) = 8 = 2^3$. It sends one bit in three letters, while the Hamming code sends four bits in seven.

**Example (Distances in Mathlib).** For $x = (1, 0, 1, 1)$ and $y = (0, 0, 1, 0)$ in $\mathbb{F}_2^4$, `hammingDist x y = 2`, and `hammingNorm (-x + y) = hammingNorm (1, 0, 0, 1) = 2`. As elements of `Hamming`, `dist (toHamming x) (toHamming y) = 2`.

### The library around it

The file `Mathlib.InformationTheory.Hamming` is the only one of the index on this subject. Linear codes are subspaces in the sense of Volume 7, and their dual codes and generator matrices use the linear algebra there.

Common errors of a learner:

- `dist x y` for `x y : ι → β` is the sup metric. For the Hamming metric, cast to `Hamming β` with `toHamming`.
- `hammingDist` is in `ℕ` and `dist` on `Hamming β` is in `ℝ`. `Hamming.dist_eq_hammingDist` connects them with a cast.
- `hammingDist_eq_hammingNorm` has `-x + y`, not `x - y`.

### Exercises

1. (A) Show that $d(x + z, y + z) = d(x, y)$ in $\mathbb{F}_q^n$.
2. (A) Show that a code of minimum distance $d$ can correct $e$ erasures, letters known to be lost, for each $e \le d - 1$.
3. (B) Prove the Singleton bound: a code of length $n$ over $q$ letters with minimum distance $d$ has $|C| \le q^{n - d + 1}$. Hint: delete the last $d - 1$ positions.
4. (B) Add a parity bit to each word of the $[7, 4, 3]$ Hamming code. Show that the result is an $[8, 4, 4]$ code.
5. (B) Let $r \ge 2$. Generalise the example to a $[2^r - 1, 2^r - 1 - r, 3]$ code, and show that it is perfect.
6. (C) Show that the repetition code of odd length $n = 2t + 1$ over $\mathbb{F}_2$ is perfect. Show that each perfect binary code of length $n$ with two words is $\{x, x + (1, \ldots, 1)\}$ for some $x$.

### Notes and history

Hamming introduced his codes and the distance in a paper of 1950. Golay found the binary Golay code, another perfect code, in 1949. The Singleton bound carries the name of R. C. Singleton.

### Reference

<?reference?>
