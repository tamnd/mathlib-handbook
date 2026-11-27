---
title: Shadows, the colex order and the Kruskal-Katona theorem
kind: theory
modules:
  - Mathlib.Combinatorics.SetFamily.Shadow
  - Mathlib.Combinatorics.Colex
  - Mathlib.Combinatorics.SetFamily.Compression.UV
  - Mathlib.Combinatorics.SetFamily.KruskalKatona
explains:
  E3: [Finset.shadow, Finset.upShadow, Finset.Colex.IsInitSeg, Finset.Colex.initSeg, UV.compress, UV.compression, Finset.kruskal_katona, Finset.kruskal_katona_lovasz_form]
  E2: [Finset.mem_shadow_iff, Finset.mem_upShadow_iff, Finset.shadow_mono, Finset.shadow_compls, Set.Sized.shadow, Finset.Colex.le_def, Finset.Colex.toColex_lt_toColex_iff_max'_mem, Finset.geomSum_lt_geomSum_iff_toColex_lt_toColex, Finset.Colex.IsInitSeg.total, Finset.Colex.shadow_initSeg, Finset.orderIsoColex, UV.IsCompressed, UV.card_compression, UV.compress_injOn, Set.Sized.uvCompression, UV.shadow_compression_subset_compression_shadow, UV.card_shadow_compression_le, Finset.UV.toColex_compress_lt_toColex, Finset.UV.isInitSeg_of_compressed, Finset.iterated_kk]
  E1: auto
families: []
requires: [V03.C03, V03.C06, V04.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Shadows, the colex order and the Kruskal-Katona theorem

### Overview

Let $\mathcal{A}$ be a family of $m$ sets, each with $r$ elements. Its shadow is the family of the sets with $r - 1$ elements that lie inside some member of $\mathcal{A}$. This section finds the least possible size of the shadow.

The Kruskal-Katona theorem gives the exact answer. In the colexicographic order on the $r$-sets of natural numbers, the first $m$ sets have the smallest shadow among all families of $m$ sets of size $r$. The proof replaces a family by a compressed family, step by step. Each step keeps the size and does not make the shadow larger. Mathlib proves the Erdős-Ko-Rado theorem of Section 3 from this theorem.

### Definitions

Fix a finite ground set $X$. An *$r$-set* is a subset of $X$ with $r$ elements, and $\binom{X}{r}$ is the family of all $r$-sets. A family is *$r$-uniform* when its members are $r$-sets.

**Definition (Shadow).** The *shadow* of a family $\mathcal{A}$ is $$\partial \mathcal{A} = \{ A \setminus \{a\} : A \in \mathcal{A},\ a \in A \}.$$ The *upper shadow* of $\mathcal{A}$ is $\partial^+ \mathcal{A} = \{ A \cup \{x\} : A \in \mathcal{A},\ x \in X \setminus A \}$.

If $\mathcal{A}$ is $r$-uniform, then $\partial \mathcal{A}$ is $(r-1)$-uniform and $\partial^+ \mathcal{A}$ is $(r+1)$-uniform. The shadow is monotone: $\mathcal{A} \subseteq \mathcal{B}$ gives $\partial \mathcal{A} \subseteq \partial \mathcal{B}$.

::: mathlib
`Finset.shadow` · `Mathlib.Combinatorics.SetFamily.Shadow`

The shadow of `𝒜 : Finset (Finset α)` is `𝒜.sup fun s => s.image (erase s)`. The notation `∂ 𝒜` is open in the scope `FinsetFamily`. The upper shadow `Finset.upShadow` needs `Fintype α`, since it adds the points outside a set.

<?decl Finset.shadow?>
:::

**Definition (Colexicographic order).** Let $A \ne B$ be finite sets of natural numbers. Then $A <_C B$ when the largest element of the symmetric difference $A \mathbin{\triangle} B$ lies in $B$. An *initial segment* of $\binom{\mathbb{N}}{r}$ is a family $\mathcal{C}$ of $r$-sets such that $B \in \mathcal{C}$, $|T| = r$ and $T <_C B$ give $T \in \mathcal{C}$.

The $3$-sets begin $$012,\ 013,\ 023,\ 123,\ 014,\ 024,\ 124,\ 034,\ 134,\ 234,\ 015, \ldots$$ where $013$ means $\{0, 1, 3\}$. The order is the order of the numbers $w(A) = \sum_{a \in A} 2^a$. Indeed, let $c$ be the largest element of $A \mathbin{\triangle} B$, and let $c \in B$. The elements above $c$ are common to $A$ and $B$, and the elements of $A$ below $c$ contribute at most $2^0 + \cdots + 2^{c-1} = 2^c - 1 < 2^c$. So $w(A) < w(B)$. Thus $<_C$ is a strict linear order, and $A \mapsto w(A)$ is an order isomorphism from the finite sets of $\mathbb{N}$ to $\mathbb{N}$.

For each $m \le \binom{n}{r}$ there is exactly one initial segment of size $m$ inside $\binom{[n]}{r}$, where $[n] = \{0, \ldots, n-1\}$: the first $m$ sets. Two initial segments are comparable for inclusion.

::: mathlib
`Finset.Colex.IsInitSeg` · `Mathlib.Combinatorics.Colex`

The type synonym `Colex (Finset α)` with the map `toColex` comes from `Mathlib.Order.Lex`. On it, `Finset.Colex.le_def` says that `s ≤ t` when each element of `s \ t` is below some element of `t \ s`. For a linear order, `Finset.Colex.toColex_lt_toColex_iff_max'_mem` gives the definition above. `IsInitSeg 𝒜 r` says that `𝒜` is `r`-sized and closed under smaller `r`-sets, and `Finset.Colex.initSeg s` is the family of the sets of size `#s` that are at most `s`. The sums of powers are in `Finset.geomSum_lt_geomSum_iff_toColex_lt_toColex`, for any base $n \ge 2$.

<?decl Finset.Colex.IsInitSeg?>
:::

**Definition (UV-compression).** Let $U, V \subseteq X$ be disjoint with $|U| = |V|$. For a set $A$, put $$C_{UV}(A) = \begin{cases} (A \cup U) \setminus V & \text{if } A \cap U = \emptyset \text{ and } V \subseteq A, \\ A & \text{otherwise.} \end{cases}$$ For a family $\mathcal{A}$, put $$C_{UV}(\mathcal{A}) = \{ A \in \mathcal{A} : C_{UV}(A) \in \mathcal{A} \} \cup \{ C_{UV}(A) : A \in \mathcal{A},\ C_{UV}(A) \notin \mathcal{A} \}.$$ The family is *$UV$-compressed* when $C_{UV}(\mathcal{A}) = \mathcal{A}$.

A compression replaces $V$ by $U$ in each member where this is possible, unless the result is already a member.

::: mathlib
`UV.compression` · `Mathlib.Combinatorics.SetFamily.Compression.UV`

Mathlib defines `UV.compress u v a` in any generalized Boolean algebra: it is `(a ⊔ u) \ v` when `Disjoint u a` and `v ≤ a`, and `a` otherwise. The family version is `UV.compression u v s`, with the notation `𝓒 u v s`, and `UV.IsCompressed u v s` means `𝓒 u v s = s`. `UV.card_compression` keeps the card, and `Set.Sized.uvCompression` keeps the uniformity when `#u = #v`.

<?decl UV.compression?>
:::

### Theorems and proofs

**Lemma (Compression keeps the size).** $|C_{UV}(\mathcal{A})| = |\mathcal{A}|$. If $\mathcal{A}$ is $r$-uniform, so is $C_{UV}(\mathcal{A})$.

*Proof.* Call the two parts of the definition $\mathcal{P}$ and $\mathcal{Q}$. The members of $\mathcal{Q}$ are not in $\mathcal{A}$, and $\mathcal{P} \subseteq \mathcal{A}$, so the parts are disjoint. The members of $\mathcal{A}$ outside $\mathcal{P}$ are the sets $A \in \mathcal{A}$ with $C_{UV}(A) \notin \mathcal{A}$. For such $A$, $C_{UV}(A) \ne A$, so $A \cap U = \emptyset$ and $V \subseteq A$. On these sets $C_{UV}$ is injective: from $D = (A \cup U) \setminus V$ the set $A$ comes back as $(D \setminus U) \cup V$. So $C_{UV}$ maps $\mathcal{A} \setminus \mathcal{P}$ bijectively onto $\mathcal{Q}$, and $|C_{UV}(\mathcal{A})| = |\mathcal{P}| + |\mathcal{Q}| = |\mathcal{A}|$. A moved set loses $|V|$ elements and gains $|U| = |V|$, so its size does not change. $\square$

Two facts follow. A set $D$ lies in $C_{UV}(\mathcal{A})$ if and only if either $D \in \mathcal{A}$ and $C_{UV}(D) \in \mathcal{A}$, or $D \notin \mathcal{A}$ and $D = C_{UV}(G)$ for some $G \in \mathcal{A}$. And if $\mathcal{A}$ is $UV$-compressed and $G \in \mathcal{A}$, then $C_{UV}(G) \in \mathcal{A}$: otherwise $C_{UV}(G) \in \mathcal{Q} \subseteq C_{UV}(\mathcal{A}) = \mathcal{A}$.

**Lemma (Compression and shadow).** Let $U, V$ be disjoint and nonempty with $|U| = |V|$. Suppose that for each $x \in U$ there is $y \in V$ such that $\mathcal{A}$ is $(U \setminus \{x\})(V \setminus \{y\})$-compressed. Then $\partial C_{UV}(\mathcal{A}) \subseteq C_{UV}(\partial \mathcal{A})$, and so $|\partial C_{UV}(\mathcal{A})| \le |\partial \mathcal{A}|$.

*Proof.* Write $C = C_{UV}$. Let $B \in \partial C(\mathcal{A})$, so $B = A' \setminus \{x\}$ with $A' \in C(\mathcal{A})$ and $x \in A'$. There are two cases.

Case 1: $B \in \partial \mathcal{A}$. To show $B \in C(\partial \mathcal{A})$, it suffices to show $C(B) \in \partial \mathcal{A}$. If $C(B) = B$ this holds. Otherwise $B \cap U = \emptyset$ and $V \subseteq B$. First, $A' \in \mathcal{A}$: if not, then $A' = C(G) \ne G$ for some $G \in \mathcal{A}$, so $A' \cap V = \emptyset$, which is false since $\emptyset \ne V \subseteq B \subseteq A'$. Suppose $x \notin U$. Then $A' \cap U = \emptyset$ and $V \subseteq A'$, so $C(A') = (A' \cup U) \setminus V$. Since $A' \in \mathcal{A}$ and $A' \in C(\mathcal{A})$, also $C(A') \in \mathcal{A}$. The point $x$ is not in $V$ (as $V \subseteq B$) and not in $U$, so $x \in C(A')$ and $C(A') \setminus \{x\} = (B \cup U) \setminus V = C(B)$. Thus $C(B) \in \partial \mathcal{A}$. Suppose $x \in U$. Take $y \in V$ as in the hypothesis. Now $A' \cap (U \setminus \{x\}) = B \cap U = \emptyset$ and $V \setminus \{y\} \subseteq A'$. Since $\mathcal{A}$ is compressed for this pair, the set $A'' = (A' \cup (U \setminus \{x\})) \setminus (V \setminus \{y\}) = ((B \setminus V) \cup U) \cup \{y\}$ lies in $\mathcal{A}$. It contains $y$, and $A'' \setminus \{y\} = (B \cup U) \setminus V = C(B)$. Thus $C(B) \in \partial \mathcal{A}$.

Case 2: $B \notin \partial \mathcal{A}$. Then $A' \notin \mathcal{A}$, since otherwise $B = A' \setminus \{x\} \in \partial \mathcal{A}$. So $A' = C(G) \ne G$ for some $G \in \mathcal{A}$. Then $U \subseteq A'$, $A' \cap V = \emptyset$ and $G = (A' \setminus U) \cup V$. Suppose $x \notin U$. Then $x \in G$, and $D = G \setminus \{x\} = (B \setminus U) \cup V$ lies in $\partial \mathcal{A}$. Since $U \subseteq B$ and $B \cap V = \emptyset$, the compression acts on $D$ and $C(D) = B$. As $B \notin \partial \mathcal{A}$, this puts $B$ in the second part of $C(\partial \mathcal{A})$. Suppose $x \in U$. Take $y \in V$ as in the hypothesis. Then $G \cap (U \setminus \{x\}) = \emptyset$ and $V \setminus \{y\} \subseteq G$, so $(G \cup (U \setminus \{x\})) \setminus (V \setminus \{y\}) = B \cup \{y\}$ lies in $\mathcal{A}$. Since $y \notin B$, this gives $B \in \partial \mathcal{A}$, a contradiction.

So $\partial C(\mathcal{A}) \subseteq C(\partial \mathcal{A})$, and the first lemma gives $|C(\partial \mathcal{A})| = |\partial \mathcal{A}|$. $\square$

**Lemma (Compressed families are initial segments).** Call a pair $(U, V)$ *useful* when $U, V$ are disjoint, nonempty, of the same size, and $\max U < \max V$. Let $\mathcal{B}$ be $r$-uniform and $UV$-compressed for each useful pair. Then $\mathcal{B}$ is an initial segment of the colex order.

*Proof.* Let $B \in \mathcal{B}$, $|T| = r$ and $T <_C B$. Put $U = T \setminus B$ and $V = B \setminus T$. They are disjoint, nonempty since $T \ne B$, and of the same size since $|T| = |B|$. The largest element of $T \mathbin{\triangle} B = U \cup V$ lies in $B$, so in $V$, and $\max U < \max V$. The pair is useful. Since $B \cap U = \emptyset$ and $V \subseteq B$, $C_{UV}(B) = (B \cup U) \setminus V = T$. As $\mathcal{B}$ is compressed, $T \in \mathcal{B}$. $\square$

**Theorem (Kruskal-Katona).** Let $\mathcal{A}$ be an $r$-uniform family of subsets of $[n]$, and let $\mathcal{C}$ be an initial segment of the $r$-sets with $|\mathcal{C}| \le |\mathcal{A}|$. Then $|\partial \mathcal{C}| \le |\partial \mathcal{A}|$.

*Proof.* Use the measure $w(\mathcal{A}) = \sum_{A \in \mathcal{A}} \sum_{a \in A} 2^a$. Let $(U, V)$ be useful. A moved set loses $\sum_{v \in V} 2^v \ge 2^{\max V}$ and gains $\sum_{u \in U} 2^u \le 2^{\max U + 1} - 1 < 2^{\max V}$. So $w(C_{UV}(\mathcal{A})) < w(\mathcal{A})$ when $C_{UV}(\mathcal{A}) \ne \mathcal{A}$.

Now run a process. If the current family is compressed for every useful pair, stop. Otherwise choose a useful pair $(U, V)$ that changes the family, with $|U|$ as small as possible, and replace the family by its compression. The measure is a natural number and drops at each step, so the process stops.

Each step satisfies the hypothesis of the second lemma. If $|U| = 1$, the pair $(U \setminus \{x\}, V \setminus \{y\})$ is $(\emptyset, \emptyset)$, and every family is compressed for it. If $|U| \ge 2$, let $x \in U$ and $y = \min V$. Then $\max(V \setminus \{y\}) = \max V > \max U \ge \max (U \setminus \{x\})$, so $(U \setminus \{x\}, V \setminus \{y\})$ is useful and smaller. By the choice of $|U|$, the family is compressed for it.

So the process ends at a family $\mathcal{A}^*$ with $|\mathcal{A}^*| = |\mathcal{A}|$, $r$-uniform, with $|\partial \mathcal{A}^*| \le |\partial \mathcal{A}|$, and compressed for every useful pair. By the third lemma $\mathcal{A}^*$ is an initial segment. Two initial segments are comparable, and $|\mathcal{C}| \le |\mathcal{A}^*|$, so $\mathcal{C} \subseteq \mathcal{A}^*$. Hence $|\partial \mathcal{C}| \le |\partial \mathcal{A}^*| \le |\partial \mathcal{A}|$. $\square$

::: mathlib
`Finset.kruskal_katona` · `Mathlib.Combinatorics.SetFamily.KruskalKatona`

The ground set is `Fin n`, and the proof follows the text. `UV.card_shadow_compression_le` is the second lemma, `Finset.UV.toColex_compress_lt_toColex` says that a useful compression moves a set down, and `Finset.UV.isInitSeg_of_compressed` is the third lemma. `Finset.iterated_kk` gives the bound for the iterated shadow.

<?decl Finset.kruskal_katona?>
:::

**Corollary (Lovász form with integers).** Let $1 \le r \le k \le n$, and let $\mathcal{A}$ be an $r$-uniform family on $[n]$ with $|\mathcal{A}| \ge \binom{k}{r}$. Then $|\partial \mathcal{A}| \ge \binom{k}{r-1}$.

*Proof.* Each $r$-set inside $[k]$ comes before each $r$-set with an element $c \ge k$ in the colex order. Indeed, the largest element of the symmetric difference of the two sets is at least $c$, so it lies in the second set. So the first $\binom{k}{r}$ sets of the order are the family $\binom{[k]}{r}$, an initial segment. Its shadow is $\binom{[k]}{r-1}$, since each $(r-1)$-set inside $[k]$ extends to an $r$-set inside $[k]$ when $r \le k$. The theorem gives $|\partial \mathcal{A}| \ge \binom{k}{r-1}$. $\square$

Lovász gave a sharper form: if $|\mathcal{A}| = \binom{x}{r}$ for a real $x \ge r$, then $|\partial \mathcal{A}| \ge \binom{x}{r-1}$. The index of this edition has no declaration for the real form. It also has no declaration for the exact minimum in the cascade form, with $m$ written as a sum of binomial coefficients $\binom{a_r}{r} + \binom{a_{r-1}}{r-1} + \cdots$ (Exercise 7 is a case).

::: mathlib
`Finset.kruskal_katona_lovasz_form` · `Mathlib.Combinatorics.SetFamily.KruskalKatona`

The Mathlib form iterates: with `i ≤ r ≤ k ≤ n`, an `r`-sized family with `k.choose r ≤ #𝒜` has `k.choose (r - i) ≤ #(∂^[i] 𝒜)`. The corollary above is the case $i = 1$.

<?decl Finset.kruskal_katona_lovasz_form?>
:::

### Examples

**Example (A small shadow and a large one).** Take $r = 3$ and $m = 4$. The family $\{012, 013, 014, 015\}$ has the shadow $\{01, 02, 12, 03, 13, 04, 14, 05, 15\}$ with $9$ sets. The first four $3$-sets in colex are $012, 013, 023, 123$, all the $3$-subsets of $\{0,1,2,3\}$. Their shadow is the family of the six $2$-subsets of $\{0, 1, 2, 3\}$. So $4$ sets of size $3$ have a shadow of at least $6$ sets.

**Example (One compression).** Let $\mathcal{A} = \{12, 13, 23\}$ on $\{0, 1, 2, 3\}$, with $U = \{0\}$ and $V = \{2\}$. Then $C_{UV}(12) = 01 \notin \mathcal{A}$, so $12$ moves to $01$. The set $13$ does not contain $2$ and stays. $C_{UV}(23) = 03 \notin \mathcal{A}$, so $23$ moves to $03$. The result is $\{01, 03, 13\}$. Both families have a shadow of three points: $\{1, 2, 3\}$ before and $\{0, 1, 3\}$ after. The measure drops from $6 + 10 + 12 = 28$ to $3 + 9 + 10 = 22$.

### The library around it

The shadow of an initial segment is again one (`Finset.Colex.shadow_initSeg`), and complements exchange the shadows (`Finset.shadow_compls`).

Common errors of a learner:

- The colex order is not the lexicographic order. In lex, $014$ comes before $023$. In colex, $023$ comes before $014$.
- The theorem asks for `Set.Sized r 𝒜`. A family with mixed sizes has a shadow with mixed sizes.
- `UV.compress u v a` changes `a` only when `u` is disjoint from `a` and `v ≤ a`. A compression with `#u ≠ #v` changes the sizes of the sets.
- The notation `∂` needs `open FinsetFamily`.

### Exercises

1. (A) Compute the shadow of $\{012, 034\}$ and of $\{012, 013\}$. Hint: the first has $6$ sets, the second $5$.
2. (A) List the $2$-subsets of $\{0, 1, 2, 3, 4\}$ in the colex order. Hint: the list starts $01, 02, 12, 03$.
3. (A) Show that $A <_C B$ if and only if $\sum_{a \in A} 2^a < \sum_{b \in B} 2^b$. Hint: the computation after the definition, with the roles of $A$ and $B$ checked in both directions.
4. (B) Let $\mathcal{A}$ be $r$-uniform on a set of $n$ elements, and $\mathcal{A}^c = \{X \setminus A : A \in \mathcal{A}\}$. Show that $\partial^+ \mathcal{A} = (\partial(\mathcal{A}^c))^c$, and deduce a lower bound for the upper shadow of $m$ sets of size $r$. Hint: complement and apply the theorem to $(n-r)$-sets.
5. (B) Find the least possible size of the shadow of $10$ sets of size $3$, and of $11$ sets of size $3$. Hint: $10 = \binom{5}{3}$, and the eleventh set in colex is $015$.
6. (B) Show that the shadow of an initial segment of $r$-sets is an initial segment of $(r-1)$-sets. Hint: if $B \setminus \{b\} \in \partial \mathcal{C}$ and $T <_C B \setminus \{b\}$, find an element to add to $T$.
7. (C) Prove the cascade form for two terms: if $m = \binom{a}{r} + \binom{b}{r-1}$ with $a > b \ge r - 1 \ge 1$, then the minimum shadow of $m$ sets of size $r$ is $\binom{a}{r-1} + \binom{b}{r-2}$. Hint: the first $m$ sets in colex are $\binom{[a]}{r}$ and the sets $S \cup \{a\}$ with $S \in \binom{[b]}{r-1}$.

### Notes and history

Kruskal proved the theorem in 1963, in a paper on the number of simplices in a complex, and Katona proved it independently in a paper of 1968. Lovász gave the form with a real parameter in his book *Combinatorial Problems and Exercises* (1979). The proof by compressions is the one in Bollobás, *Combinatorics* (1986). The Authors line of the Mathlib file `KruskalKatona.lean` names Bhavik Mehta and Yaël Dillies.

### Reference

<?reference?>
