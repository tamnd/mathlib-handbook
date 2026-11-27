---
title: Intersecting families, correlation and shattering
kind: theory
modules:
  - Mathlib.Combinatorics.SetFamily.Intersecting
  - Mathlib.Combinatorics.SetFamily.HarrisKleitman
  - Mathlib.Combinatorics.SetFamily.Kleitman
  - Mathlib.Combinatorics.SetFamily.FourFunctions
  - Mathlib.Combinatorics.SetFamily.Shatter
  - Mathlib.Combinatorics.SetFamily.DualVC
  - Mathlib.Combinatorics.SetFamily.Compression.Down
explains:
  E3: [Set.Intersecting, Set.Intersecting.card_le, Finset.erdos_ko_rado, IsUpperSet.le_card_inter_finset, Finset.card_biUnion_le_of_intersecting, four_functions_theorem, Finset.Shatters, Finset.shatterer, Finset.vcDim, Finset.card_le_card_shatterer, Finset.card_shatterer_le_sum_vcDim, Down.compression]
  E2: [Set.Intersecting.is_max_iff_card_eq, Set.Intersecting.exists_card_eq, Set.Intersecting.isUpperSet', Set.Intersecting.compl_notMem, Set.intersecting_insert, IsLowerSet.le_card_inter_finset, IsLowerSet.card_inter_le_finset, IsUpperSet.card_inter_le_finset, Finset.four_functions_theorem, Finset.le_card_infs_mul_card_sups, fkg, holley, Finset.card_le_card_diffs, Finset.mem_shatterer, Finset.isLowerSet_shatterer, Finset.shatterer_eq, Finset.Shatters.card_le_vcDim, Finset.Shatters.mono_left, Finset.shatterer_compress_subset_shatterer, Finset.vcDim_compress_le, Finset.dualFamily, Finset.vcDim_dualFamily_le, Down.mem_compression, Down.card_compression, Finset.memberSubfamily, Finset.nonMemberSubfamily, Finset.mem_memberSubfamily, Finset.mem_nonMemberSubfamily, Finset.card_memberSubfamily_add_card_nonMemberSubfamily, IsLowerSet.memberSubfamily_subset_nonMemberSubfamily]
  E1: auto
families: []
requires: [V03.C03, V03.C04, V03.C06, V04.C01, V04.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Intersecting families, correlation and shattering

### Overview

A family is intersecting when any two of its members meet. On an $n$-set, an intersecting family has at most $2^{n-1}$ members, since it cannot hold a set and its complement. For $r$-sets with $n \ge 2r$, the Erdős-Ko-Rado theorem gives the sharp bound $\binom{n-1}{r-1}$, attained by all the $r$-sets through one point. The proof by Katona places the points on a circle.

The second topic is correlation. Two upper sets of subsets are positively correlated: a random set that lies in one is more likely to lie in the other. This is the Harris-Kleitman inequality. It gives a sharp bound for a union of $k$ intersecting families. The four functions theorem and the FKG inequality extend it.

The third topic is shattering. A family shatters a set $S$ when it cuts out every subset of $S$. The lemma of Pajor says that a family shatters at least as many sets as it has members. The Sauer-Shelah lemma follows.

### Definitions

Fix a finite set $X$ with $n$ elements.

**Definition (Intersecting family).** A family $\mathcal{A}$ of subsets of $X$ is *intersecting* when $A \cap B \ne \emptyset$ for all $A, B \in \mathcal{A}$, with $A = B$ allowed.

So an intersecting family does not contain $\emptyset$. The *star* at a point $x$ is the family of all sets that contain $x$. It is intersecting and has $2^{n-1}$ members.

::: mathlib
`Set.Intersecting` · `Mathlib.Combinatorics.SetFamily.Intersecting`

Mathlib defines `s.Intersecting` for a set `s` in a meet-semilattice with a bottom element: `∀ a ∈ s, ∀ b ∈ s, ¬Disjoint a b`. For a family of finsets the lattice is `Finset α`. The case $a = b$ gives $a \ne \bot$.

<?decl Set.Intersecting?>
:::

**Definition (Upper and lower sets).** A family $\mathcal{A}$ is an *upper set* when $A \in \mathcal{A}$ and $A \subseteq B \subseteq X$ give $B \in \mathcal{A}$, and a *lower set* when $A \in \mathcal{A}$ and $B \subseteq A$ give $B \in \mathcal{A}$.

These are the upper and lower sets of Volume 4, Chapter 1. In Mathlib they are `IsUpperSet` and `IsLowerSet` of `Mathlib.Order.UpperLower.Basic`, applied to the coercion of a finset family to a set.

**Definition (Shattering).** A family $\mathcal{A}$ *shatters* a set $S$ when for each $T \subseteq S$ there is $A \in \mathcal{A}$ with $S \cap A = T$. The *VC dimension* of $\mathcal{A}$ is the largest size of a set that $\mathcal{A}$ shatters.

The family of shattered sets is a lower set: if $\mathcal{A}$ shatters $S$ and $S' \subseteq S$, it shatters $S'$, since $S' \cap A = T'$ follows from $S \cap A = T'$.

::: mathlib
`Finset.Shatters` · `Mathlib.Combinatorics.SetFamily.Shatter`

`𝒜.Shatters s` is `∀ ⦃t⦄, t ⊆ s → ∃ u ∈ 𝒜, s ∩ u = t`. The finset `𝒜.shatterer` collects the shattered sets, with `Finset.mem_shatterer`, and `𝒜.vcDim` is `𝒜.shatterer.sup card`. `Finset.isLowerSet_shatterer` is the remark above.

<?decl Finset.Shatters?>
:::

### Theorems and proofs

**Theorem (Intersecting families).** An intersecting family $\mathcal{A}$ on $X$ has $|\mathcal{A}| \le 2^{n-1}$. If $n \ge 1$ and $\mathcal{A}$ is a maximal intersecting family, then $\mathcal{A}$ is an upper set with $2^{n-1}$ members.

*Proof.* The $2^n$ subsets of $X$ fall into $2^{n-1}$ pairs $\{A, X \setminus A\}$. Since $A \cap (X \setminus A) = \emptyset$, the family contains at most one set of each pair. Let $\mathcal{A}$ be maximal. If $A \in \mathcal{A}$ and $A \subseteq B$, then $B$ meets each set that $A$ meets, so $\mathcal{A} \cup \{B\}$ is intersecting and $B \in \mathcal{A}$. Now take any pair $\{A, X \setminus A\}$ with $A \notin \mathcal{A}$. If $A = \emptyset$, then $X \setminus A = X$, which lies in $\mathcal{A}$ since $\mathcal{A}$ is a nonempty upper set (it is nonempty, as $\{X\}$ is intersecting). Otherwise maximality gives $C \in \mathcal{A}$ disjoint from $A$, so $C \subseteq X \setminus A$ and $X \setminus A \in \mathcal{A}$. So $\mathcal{A}$ holds one set of each pair. $\square$

::: mathlib
`Set.Intersecting.card_le` · `Mathlib.Combinatorics.SetFamily.Intersecting`

The statement is `2 * #s ≤ Fintype.card α` for an intersecting finset `s` of a finite Boolean algebra `α`. `Set.Intersecting.is_max_iff_card_eq` says that an intersecting family is maximal exactly when `2 * #s = Fintype.card α`, and `Set.Intersecting.isUpperSet'` that a maximal one is an upper set.

<?decl Set.Intersecting.card_le?>
:::

**Theorem (Erdős-Ko-Rado).** Let $1 \le r$ and $2r \le n$. An intersecting family of $r$-subsets of $X$ has at most $\binom{n-1}{r-1}$ members.

*Proof.* Identify the positions $0, 1, \ldots, n-1$ with the integers modulo $n$. For a bijection $\sigma : X \to \mathbb{Z}/n$ and a position $i$, the *arc* $\sigma_i$ is the $r$-set $\sigma^{-1}(\{i, i+1, \ldots, i+r-1\})$.

Claim: for each $\sigma$, at most $r$ positions $i$ have $\sigma_i \in \mathcal{A}$. If no arc lies in $\mathcal{A}$, the claim holds. Otherwise rotate the positions so that $\sigma_0 \in \mathcal{A}$. An arc $\sigma_j$ meets $\sigma_0$ only for $j \in \{-(r-1), \ldots, r-1\}$. Pair $\sigma_j$ with $\sigma_{j-r}$ for $1 \le j \le r - 1$. The two arcs of a pair cover the $2r$ consecutive positions $j - r, \ldots, j + r - 1$, which are distinct modulo $n$ since $2r \le n$. So the two arcs of a pair are disjoint, and at most one of them lies in $\mathcal{A}$. The pairs cover all arcs that meet $\sigma_0$, other than $\sigma_0$. So at most $1 + (r - 1) = r$ arcs lie in $\mathcal{A}$.

Now count the pairs $(\sigma, i)$ with $\sigma_i \in \mathcal{A}$. By the claim there are at most $r \cdot n!$. For fixed $A \in \mathcal{A}$ and $i$, the bijections with $\sigma_i = A$ map $A$ onto the $r$ positions of the arc and the rest onto the rest, so there are $r!\,(n-r)!$ of them. So $$|\mathcal{A}| \cdot n \cdot r!\,(n-r)! \le r \cdot n!, \qquad |\mathcal{A}| \le \frac{r\,(n-1)!}{r!\,(n-r)!} = \binom{n-1}{r-1}. \qquad \square$$

::: mathlib
`Finset.erdos_ko_rado` · `Mathlib.Combinatorics.SetFamily.KruskalKatona`

The statement is for `𝒜 : Finset (Finset (Fin n))`, intersecting and `r`-sized, with `r ≤ n / 2`, and it concludes `#𝒜 ≤ (n - 1).choose (r - 1)`. The proof in Mathlib is not the proof above. It applies the Lovász form of Section 1, `Finset.kruskal_katona_lovasz_form`, to the family of complements, which is $(n-r)$-sized, with $i = n - 2r$. The iterated shadow of the complements is disjoint from $\mathcal{A}$, and the sizes then add up to more than $\binom{n}{r}$.

<?decl Finset.erdos_ko_rado?>
:::

**Theorem (Harris-Kleitman).** Let $\mathcal{A}, \mathcal{B}$ be upper sets of subsets of $X$. Then $|\mathcal{A}|\,|\mathcal{B}| \le 2^n\, |\mathcal{A} \cap \mathcal{B}|$.

*Proof.* Induction on $n$. For $n = 0$ each family is $\emptyset$ or $\{\emptyset\}$, and the inequality is $0 \le 0$ or $1 \le 1$. For the step, pick $a \in X$ and put $X' = X \setminus \{a\}$. For a family $\mathcal{F}$ on $X$ let $\mathcal{F}_0 = \{F \in \mathcal{F} : a \notin F\}$ and $\mathcal{F}_1 = \{F \setminus \{a\} : F \in \mathcal{F},\ a \in F\}$, two families on $X'$. Then $|\mathcal{F}| = |\mathcal{F}_0| + |\mathcal{F}_1|$, and $(\mathcal{A} \cap \mathcal{B})_i = \mathcal{A}_i \cap \mathcal{B}_i$. If $\mathcal{A}$ is an upper set, then $\mathcal{A}_0$ and $\mathcal{A}_1$ are upper sets on $X'$, and $\mathcal{A}_0 \subseteq \mathcal{A}_1$ since $F \in \mathcal{A}$ gives $F \cup \{a\} \in \mathcal{A}$. Write $a_i = |\mathcal{A}_i|$ and $b_i = |\mathcal{B}_i|$, so $a_0 \le a_1$ and $b_0 \le b_1$. The induction hypothesis on $X'$ gives $$2^n |\mathcal{A} \cap \mathcal{B}| = 2 \cdot 2^{n-1} \left( |\mathcal{A}_0 \cap \mathcal{B}_0| + |\mathcal{A}_1 \cap \mathcal{B}_1| \right) \ge 2(a_0 b_0 + a_1 b_1).$$ Finally $2(a_0 b_0 + a_1 b_1) - (a_0 + a_1)(b_0 + b_1) = (a_1 - a_0)(b_1 - b_0) \ge 0$. $\square$

For an upper set $\mathcal{A}$ and a lower set $\mathcal{B}$ the inequality turns around. The complement $\mathcal{B}' = 2^X \setminus \mathcal{B}$ is an upper set, so $|\mathcal{A}|(2^n - |\mathcal{B}|) \le 2^n (|\mathcal{A}| - |\mathcal{A} \cap \mathcal{B}|)$, that is, $2^n |\mathcal{A} \cap \mathcal{B}| \le |\mathcal{A}|\,|\mathcal{B}|$.

::: mathlib
`IsUpperSet.le_card_inter_finset` · `Mathlib.Combinatorics.SetFamily.HarrisKleitman`

The statement is `#𝒜 * #ℬ ≤ 2 ^ Fintype.card α * #(𝒜 ∩ ℬ)` for `IsUpperSet ↑𝒜` and `IsUpperSet ↑ℬ`. Mathlib proves the form for two lower sets, `IsLowerSet.le_card_inter_finset`, by the induction above, with `Finset.memberSubfamily a 𝒜` for $\mathcal{F}_1$ and `Finset.nonMemberSubfamily a 𝒜` for $\mathcal{F}_0$. `IsLowerSet.card_inter_le_finset` is the mixed form.

<?decl IsUpperSet.le_card_inter_finset?>
:::

**Theorem (Kleitman).** Let $n \ge 1$, $k \le n$, and let $\mathcal{A}_1, \ldots, \mathcal{A}_k$ be intersecting families on $X$. Then $|\mathcal{A}_1 \cup \cdots \cup \mathcal{A}_k| \le 2^n - 2^{n-k}$.

*Proof.* Enlarge each $\mathcal{A}_i$ to a maximal intersecting family $\mathcal{A}_i'$. By the theorem above it is an upper set with $2^{n-1}$ members. Its complement $\mathcal{B}_i = 2^X \setminus \mathcal{A}_i'$ is a lower set with $2^{n-1}$ members. An intersection of lower sets is a lower set. By the form of Harris-Kleitman for two lower sets and induction on $j$, $$|\mathcal{B}_1 \cap \cdots \cap \mathcal{B}_{j+1}| \ge \frac{|\mathcal{B}_1 \cap \cdots \cap \mathcal{B}_j|\, 2^{n-1}}{2^n} \ge 2^{n-j-1}.$$ So $|\bigcup_i \mathcal{A}_i| \le |\bigcup_i \mathcal{A}_i'| = 2^n - |\bigcap_i \mathcal{B}_i| \le 2^n - 2^{n-k}$. $\square$

::: mathlib
`Finset.card_biUnion_le_of_intersecting` · `Mathlib.Combinatorics.SetFamily.Kleitman`

The families are `f i` for `i` in a finset `s` of indices, and the bound is `2 ^ Fintype.card α - 2 ^ (Fintype.card α - #s)`, with `Nonempty α`.

<?decl Finset.card_biUnion_le_of_intersecting?>
:::

Mathlib also has the four functions theorem of Ahlswede and Daykin. Let $L$ be a finite distributive lattice and $f_1, f_2, f_3, f_4 \ge 0$ functions on $L$ with $f_1(a) f_2(b) \le f_3(a \wedge b) f_4(a \vee b)$ for all $a, b$. Then for all subsets $S, T \subseteq L$, $$\Big(\sum_{a \in S} f_1(a)\Big)\Big(\sum_{b \in T} f_2(b)\Big) \le \Big(\sum_{c \in S \wedge T} f_3(c)\Big)\Big(\sum_{d \in S \vee T} f_4(d)\Big),$$ where $S \wedge T = \{a \wedge b\}$ and $S \vee T = \{a \vee b\}$. With all $f_i = 1$ this is the inequality of Daykin, $|S|\,|T| \le |S \wedge T|\,|S \vee T|$. The FKG inequality follows: if $\mu \ge 0$ satisfies $\mu(a)\mu(b) \le \mu(a \wedge b)\mu(a \vee b)$ and $f, g \ge 0$ are monotone, then $(\sum \mu f)(\sum \mu g) \le (\sum \mu)(\sum \mu f g)$. With $\mu = 1$ and $f, g$ the indicators of two upper sets, it is the Harris-Kleitman inequality. This section does not prove these theorems.

::: mathlib
`four_functions_theorem` · `Mathlib.Combinatorics.SetFamily.FourFunctions`

The general form is for a `DistribLattice α` and values in a linearly ordered commutative semiring `β`. The proof first proves `Finset.four_functions_theorem` on a power set, by induction on the ground set, and then transfers it to a finite distributive lattice with Birkhoff's representation theorem. The corollaries are `Finset.le_card_infs_mul_card_sups` (Daykin), `holley`, `fkg` and `Finset.card_le_card_diffs` (Marica-Schönheim).

<?decl four_functions_theorem?>
:::

**Theorem (Pajor).** Every family $\mathcal{A}$ of subsets of $X$ shatters at least $|\mathcal{A}|$ sets.

*Proof.* Induction on $n$. For $n = 0$, either $\mathcal{A} = \emptyset$, or $\mathcal{A} = \{\emptyset\}$, which shatters $\emptyset$. For the step pick $a \in X$, and form two families on $X' = X \setminus \{a\}$: $$\mathcal{A}' = \{A \setminus \{a\} : A \in \mathcal{A}\}, \qquad \mathcal{A}'' = \{A \subseteq X' : A \in \mathcal{A} \text{ and } A \cup \{a\} \in \mathcal{A}\}.$$ The map $A \mapsto A \setminus \{a\}$ from $\mathcal{A}$ onto $\mathcal{A}'$ is two-to-one over $\mathcal{A}''$ and one-to-one elsewhere, so $|\mathcal{A}| = |\mathcal{A}'| + |\mathcal{A}''|$. By induction, $\mathcal{A}'$ and $\mathcal{A}''$ shatter at least $|\mathcal{A}'|$ and $|\mathcal{A}''|$ sets inside $X'$.

If $\mathcal{A}'$ shatters $S \subseteq X'$, so does $\mathcal{A}$: for $T \subseteq S$ take $A \in \mathcal{A}$ with $S \cap (A \setminus \{a\}) = T$, and then $S \cap A = T$ since $a \notin S$. If $\mathcal{A}''$ shatters $S$, then $\mathcal{A}$ shatters $S \cup \{a\}$. For $T \subseteq S \cup \{a\}$ with $a \notin T$, take $A \in \mathcal{A}''$ with $S \cap A = T$; then $A \in \mathcal{A}$ and $(S \cup \{a\}) \cap A = T$. For $T = T' \cup \{a\}$, take $A \in \mathcal{A}''$ with $S \cap A = T'$, and use $A \cup \{a\} \in \mathcal{A}$. The sets of the first kind avoid $a$ and those of the second kind contain $a$. So $\mathcal{A}$ shatters at least $|\mathcal{A}'| + |\mathcal{A}''| = |\mathcal{A}|$ sets. $\square$

**Corollary (Sauer-Shelah).** If $\mathcal{A}$ has VC dimension $d$, then $|\mathcal{A}| \le \sum_{k=0}^{d} \binom{n}{k}$.

*Proof.* Every shattered set has at most $d$ elements, and there are $\sum_{k \le d} \binom{n}{k}$ such subsets of $X$. Apply the theorem. $\square$

::: mathlib
`Finset.card_le_card_shatterer` · `Mathlib.Combinatorics.SetFamily.Shatter`

The statement is `#𝒜 ≤ #𝒜.shatterer`. Mathlib proves it with the down-compression `Down.compression a 𝒜`, which keeps the size of the family (`Down.card_compression`) and can only lose shattered sets (`Finset.shatterer_compress_subset_shatterer`). The bound of the corollary is `Finset.card_shatterer_le_sum_vcDim`: `#𝒜.shatterer ≤ ∑ k ≤ 𝒜.vcDim, (Fintype.card α).choose k`. The index of this edition has no declaration named after Sauer and Shelah.

<?decl Finset.card_le_card_shatterer?>
:::

::: mathlib
`Down.compression` · `Mathlib.Combinatorics.SetFamily.Compression.Down`

The down-compression at `a` removes `a` from each member where the result is new. By `Down.mem_compression`, `s` lies in it when either `s ∈ 𝒜` and `s.erase a ∈ 𝒜`, or `s ∉ 𝒜` and `insert a s ∈ 𝒜`.

<?decl Down.compression?>
:::

### Examples

**Example (Two extremal families for EKR).** For $n = 4$ and $r = 2$ the bound is $\binom{3}{1} = 3$. The star $\{01, 02, 03\}$ attains it, and so does the triangle $\{01, 02, 12\}$, which is not a star. For $n = 2r$ any choice of one set from each complementary pair of $r$-sets gives an intersecting family of size $\binom{2r}{r}/2 = \binom{2r-1}{r-1}$. For $n < 2r$ the theorem fails: any two $r$-sets meet, and all $\binom{n}{r}$ of them form an intersecting family.

**Example (Intervals).** Let $\mathcal{I}$ be the family of the intervals $\{i, i+1, \ldots, j\}$ of $\{0, \ldots, n-1\}$ with $i \le j$, together with $\emptyset$. It shatters each pair $a < b$: the traces $\emptyset$, $\{a\}$, $\{b\}$, $\{a, b\}$ come from $\emptyset$, $\{a\}$, $\{b\}$ and $\{a, \ldots, b\}$. It shatters no triple $a < b < c$, since an interval that contains $a$ and $c$ contains $b$. So $d = 2$, and $|\mathcal{I}| = \binom{n}{2} + n + 1$ attains the Sauer-Shelah bound.

### The library around it

The file `Mathlib.Combinatorics.SetFamily.DualVC` bounds the VC dimension of the dual family: `Finset.vcDim_dualFamily_le` says that if $\mathcal{A}$ has VC dimension at most $d$, the family `𝒜.dualFamily X` of the sets $\{A \in \mathcal{A} : x \in A\}$ has VC dimension at most $2^{d+1} - 1$.

Common errors of a learner:

- An intersecting family in Mathlib must avoid `⊥`, and `{⊥}` is not intersecting. `Set.intersecting_insert` shows the condition for one new member.
- The EKR theorem needs `r ≤ n / 2`, with the division of `ℕ`.
- The Harris-Kleitman inequality is for upper sets of all of `Finset α`, with `Fintype α`.

### Exercises

1. (A) Show that the family of all subsets of $\{0, 1, 2\}$ with at least two elements is a maximal intersecting family. Hint: count, and use the first theorem.
2. (A) List all intersecting families of $2$-subsets of $\{0, 1, 2, 3\}$ with $3$ members. Hint: four stars and four triangles.
3. (A) Compute the VC dimension of the family of all subsets of $X$ with at most $d$ elements, and check that it attains the Sauer-Shelah bound.
4. (B) Show that an intersecting family of $r$-sets with $n \ge 2r$ that is contained in no star can still have $\binom{n-1}{r-1}$ members when $r = 2$ and $n = 4$, but not when $r = 2$ and $n \ge 5$. Hint: a triangle has $3$ members.
5. (B) Prove the mixed Harris-Kleitman inequality $2^n |\mathcal{A} \cap \mathcal{B}| \le |\mathcal{A}|\,|\mathcal{B}|$ for $\mathcal{A}$ upper and $\mathcal{B}$ lower in full, and give an example with strict inequality.
6. (B) Show that the family $\mathcal{A}''$ of the proof of Pajor's theorem satisfies $\mathcal{A}'' \subseteq \mathcal{A}'$, and that $|\mathcal{A}| = |\mathcal{A}'| + |\mathcal{A}''|$.
7. (C) Prove the case $n = 2r$ of the Erdős-Ko-Rado theorem without the circle. Hint: pair each $r$-set with its complement.

### Notes and history

Erdős, Ko and Rado proved their theorem in a paper published in 1961, and Katona gave the proof with cyclic orders in 1972. Harris proved the correlation inequality in 1960 in work on percolation, and Kleitman proved it for set families in 1966. The FKG inequality is due to Fortuin, Kasteleyn and Ginibre (1971), and the four functions theorem to Ahlswede and Daykin (1978). Sauer and Shelah proved their lemma independently in 1972. The Authors line of the Mathlib files on intersecting families, the Harris-Kleitman inequality, the four functions theorem and shattering names Yaël Dillies.

### Reference

<?reference?>
