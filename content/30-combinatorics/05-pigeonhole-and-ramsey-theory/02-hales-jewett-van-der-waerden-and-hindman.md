---
title: Hales-Jewett, van der Waerden and Hindman
kind: theory
modules:
  - Mathlib.Combinatorics.HalesJewett
  - Mathlib.Combinatorics.Hindman
explains:
  E3: [Combinatorics.Line, Combinatorics.Line.IsMono, Combinatorics.Line.exists_mono_in_high_dimension, Combinatorics.exists_mono_homothetic_copy, Hindman.FS, Hindman.exists_FS_of_large, Hindman.exists_FS_of_finite_cover, Ultrafilter.add]
  E2: [Combinatorics.Line.idxFun, Combinatorics.Line.proper, Combinatorics.Line.AlmostMono, Combinatorics.Line.ColorFocused, Combinatorics.Line.diagonal, Combinatorics.Line.map, Combinatorics.Line.prod, Combinatorics.Line.horizontal, Combinatorics.Line.vertical, Combinatorics.Line.toSubspace, Combinatorics.Subspace, Combinatorics.Subspace.IsMono, Combinatorics.Subspace.exists_mono_in_high_dimension, Combinatorics.Subspace.exists_mono_in_high_dimension_fin, Hindman.FP, Hindman.exists_FP_of_large, Hindman.exists_FP_of_finite_cover, Hindman.exists_idempotent_ultrafilter_le_FS, Hindman.exists_idempotent_ultrafilter_le_FP, Hindman.FS_partition_regular, Hindman.FP_partition_regular, Hindman.FS.add, Hindman.FS_iter_tail_sub_FS, Ultrafilter.mul, Ultrafilter.eventually_add, Ultrafilter.eventually_mul, Ultrafilter.semigroup, Ultrafilter.addSemigroup, Ultrafilter.continuous_mul_left, Ultrafilter.continuous_add_left]
  E1: auto
families: []
requires: [V03.C03, V05.C01, V13.C02, V13.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Hales-Jewett, van der Waerden and Hindman

### Overview

Section 1 coloured pairs. This section colours points. Van der Waerden's theorem says that in each colouring of the natural numbers with finitely many colours, some colour class contains arithmetic progressions of every length. Hindman's theorem says that some colour class contains all finite sums of an infinite sequence.

The Hales-Jewett theorem is the combinatorial core of van der Waerden's theorem. It finds a monochromatic *combinatorial line* in the cube $\alpha^n$ of words over a finite alphabet, by a double induction without arithmetic. Van der Waerden follows by adding up the letters of a word.

Hindman's theorem uses the compact semigroup of ultrafilters. An idempotent ultrafilter gives the sequence directly.

### Definitions

**Definition (Combinatorial line).** Let $\alpha$ be a finite alphabet and $\iota$ a finite set of coordinates. A *combinatorial line* in $\alpha^\iota$ is given by a word $w : \iota \to \alpha \cup \{\ast\}$ in which the symbol $\ast$ occurs at least once. For $x \in \alpha$ the point $w(x) \in \alpha^\iota$ replaces each $\ast$ by $x$. The line is the set $\{w(x) : x \in \alpha\}$, which has $|\alpha|$ points. A line is *monochromatic* for a colouring $C$ of $\alpha^\iota$ if $C(w(x))$ does not depend on $x$.

For example, with $\alpha = \{0, 1, 2\}$ and $\iota = \{1, 2, 3, 4\}$, the word $w = 1{\ast}0{\ast}$ gives the line $1000$, $1101$, $1202$. The coordinates with $\ast$ are the *moving* coordinates.

::: mathlib
`Combinatorics.Line` · `Mathlib.Combinatorics.HalesJewett`

`Line α ι` is a structure with `idxFun : ι → Option α` and `proper : ∃ i, idxFun i = none`. The value `none` plays the role of $\ast$. `Line.diagonal α ι` has every coordinate moving, and `Line.map` changes the alphabet.

<?decl Combinatorics.Line?>
:::

::: mathlib
`Combinatorics.Line.IsMono` · `Mathlib.Combinatorics.HalesJewett`

For `C : (ι → α) → κ`, `l.IsMono C` is `∃ c, ∀ x, C (l x) = c`. The proof below colours with a type of colourings.

<?decl Combinatorics.Line.IsMono?>
:::

**Definition (Finite sums).** Let $(M, +)$ be a semigroup and $a = (a_0, a_1, a_2, \dots)$ a sequence in $M$. The set $FS(a)$ of *finite sums* of $a$ consists of the sums $a_{n_1} + a_{n_2} + \dots + a_{n_k}$ with $k \ge 1$ and $n_1 < n_2 < \dots < n_k$.

Each index is used at most once. The order of the terms follows the indices, which matters when $M$ is not commutative.

::: mathlib
`Hindman.FS` · `Mathlib.Combinatorics.Hindman`

`Hindman.FS a m`, for `a : Stream' M`, is an inductive predicate with three rules: `FS a a.head`; `FS a.tail m → FS a m`; and `FS a.tail m → FS a (a.head + m)`. The rules take the first term, skip it, or add it in front. The multiplicative form is `Hindman.FP`.

<?decl Hindman.FS?>
:::

### Theorems and proofs

**Theorem (Hales-Jewett).** For each finite alphabet $\alpha$ and each finite set $\kappa$ of colours there is a finite set $\iota$ such that each colouring of $\alpha^\iota$ by $\kappa$ has a monochromatic combinatorial line.

*Proof.* The proof is by induction on $|\alpha|$. If $\alpha$ is empty or has one element, then every line is monochromatic, and any nonempty $\iota$ works. For the induction step, assume the theorem for $\alpha$ and every finite set of colours, and prove it for the alphabet $\alpha' = \alpha \cup \{\ast\}$, with one new letter $\ast$. Fix $\kappa$ with $r$ colours.

Call a line $L$ in $(\alpha')^\iota$ *almost monochromatic* of colour $c$ if $C(L(x)) = c$ for each $x \in \alpha$. The point $L(\ast)$ is its *endpoint*, and its colour is not constrained. A family of $k$ almost monochromatic lines is *colour focused* if the lines have the same endpoint $f$ and $k$ distinct colours.

*Claim.* For each $k \ge 0$ there is a finite $\iota_k$ such that each colouring of $(\alpha')^{\iota_k}$ has a monochromatic line or a colour focused family of $k$ lines.

The claim for $k = r + 1$ proves the theorem, because $r + 1$ distinct colours do not exist. The claim for $k = 0$ holds with any $\iota$, since the empty family is colour focused.

*Proof of the claim, from $k$ to $k + 1$.* Let $\iota = \iota_k$ and let $N = r^{|\alpha'|^{|\iota|}}$, the number of colourings of $(\alpha')^\iota$. By the induction hypothesis on the alphabet, there is a finite $\iota'$ such that each colouring of $\alpha^{\iota'}$ with $N$ colours has a monochromatic line. Take the coordinate set $\iota \sqcup \iota'$, so a point is a pair $(x, y)$ with $x \in (\alpha')^\iota$ and $y \in (\alpha')^{\iota'}$.

Let $C$ be a colouring of $(\alpha')^{\iota \sqcup \iota'}$. For $y \in \alpha^{\iota'}$, the map $x \mapsto C(x, y)$ is a colouring of $(\alpha')^\iota$, one of $N$. This colours $\alpha^{\iota'}$ with $N$ colours, so there is a line $l'$ in $\alpha^{\iota'}$ on which this colouring is constant. So there is one colouring $C'$ of $(\alpha')^\iota$ with $C(x, l'(a)) = C'(x)$ for each $x$ and each $a \in \alpha$.

Apply the claim for $k$ to $C'$. If $C'$ has a monochromatic line $L$, then the line $a \mapsto (L(a), l'(b))$ for a fixed $b \in \alpha$ is monochromatic for $C$. Otherwise $C'$ has a colour focused family $L_1, \dots, L_k$ with endpoint $f$ and colours $c_1, \dots, c_k$. If $C'(f) = c_i$ for some $i$, then $L_i$ is monochromatic for $C'$, and the previous case applies. Suppose $C'(f)$ is a new colour. Extend $l'$ to the alphabet $\alpha'$, so that $l'(\ast)$ is defined. Consider the $k + 1$ lines
$$M_i(a) = (L_i(a), l'(a)) \quad (1 \le i \le k), \qquad M_0(a) = (f, l'(a)).$$
For $a \in \alpha$, $C(M_i(a)) = C'(L_i(a)) = c_i$ and $C(M_0(a)) = C'(f)$. So all $k + 1$ lines are almost monochromatic, with distinct colours. Their endpoints are $M_i(\ast) = (L_i(\ast), l'(\ast)) = (f, l'(\ast))$ and $M_0(\ast) = (f, l'(\ast))$, the same point. So they form a colour focused family of $k + 1$ lines. $\square$

::: mathlib
`Combinatorics.Line.exists_mono_in_high_dimension` · `Mathlib.Combinatorics.HalesJewett`

For finite `α` and `κ`, `∃ ι (_ : Fintype ι), ∀ C : (ι → α) → κ, ∃ l : Line α ι, l.IsMono C`. The proof in the file is the one above. The alphabet $\alpha'$ is `Option α`. The structures `Line.AlmostMono` and `Line.ColorFocused` hold the two notions of the claim, and `Line.prod`, `Line.vertical` and `Line.horizontal` build the lines $M_i$, $M_0$ and the line of the first case.

<?decl Combinatorics.Line.exists_mono_in_high_dimension?>
:::

**Corollary (van der Waerden).** Colour $\mathbb{N}$ with finitely many colours, and let $k \ge 1$. There are $a \ge 1$ and $b$ such that $b, b + a, b + 2a, \dots, b + (k-1)a$ have the same colour.

*Proof.* Let $\alpha = \{0, 1, \dots, k-1\}$ and take $\iota$ from the Hales-Jewett theorem. Colour a word $x \in \alpha^\iota$ by the colour of $\sum_{i \in \iota} x_i \in \mathbb{N}$. There is a monochromatic line $w$. Let $a \ge 1$ be the number of moving coordinates of $w$ and $b$ the sum of the fixed letters. Then $\sum_i w(s)_i = a s + b$ for $s \in \alpha$. So the numbers $a s + b$ for $s = 0, \dots, k-1$ have one colour. $\square$

The same proof works for any finite set $S$ in a commutative monoid: take $\alpha = S$, and the set $\{a s + b : s \in S\}$ is a monochromatic *homothetic copy* of $S$.

::: mathlib
`Combinatorics.exists_mono_homothetic_copy` · `Mathlib.Combinatorics.HalesJewett`

For `[AddCommMonoid M]`, `S : Finset M`, `[Finite κ]` and `C : M → κ`, the statement `∃ a > 0, ∃ b c, ∀ s ∈ S, C (a • s + b) = c`. Here `a` is a natural number and the colouring is of all of `M`. The finite form, with a bound $W$ such that each colouring of $\{1, \dots, W\}$ works, is not stated; the file lists it as a task for later.

<?decl Combinatorics.exists_mono_homothetic_copy?>
:::

The next theorem works with ultrafilters on $M$, as in Volume 13, Chapter 2. Let $\beta M$ be the set of ultrafilters on $M$, with the topology whose basic open sets are $\{U : A \in U\}$ for $A \subseteq M$. This space is compact and Hausdorff.

**Definition (Sum of ultrafilters).** For ultrafilters $U, V$ on a semigroup $M$, let $U + V$ be the ultrafilter of the sets $A$ with
$$\{m : \{m' : m + m' \in A\} \in V\} \in U.$$

This is an ultrafilter, and the addition is associative. For each fixed $V$, the map $U \mapsto U + V$ is continuous. The map $V \mapsto U + V$ is not continuous in general.

::: mathlib
`Ultrafilter.add` · `Mathlib.Combinatorics.Hindman`

A definition of `Add (Ultrafilter M)` for `[Add M]`, by `(· + ·) <$> U <*> V` in the monad of ultrafilters. It is a local instance of the file. The lemma `Ultrafilter.eventually_add` unfolds it to the formula above. `Ultrafilter.addSemigroup` gives the semigroup, and `Ultrafilter.continuous_add_left V` is the continuity of `fun x ↦ x + V`. The multiplicative forms are `Ultrafilter.mul`, `Ultrafilter.semigroup` and `Ultrafilter.continuous_mul_left`.

<?decl Ultrafilter.add?>
:::

**Lemma (Ellis and Numakura).** Let $S$ be a nonempty compact Hausdorff semigroup in which each map $x \mapsto x r$ is continuous. Then $S$ has an idempotent: $e e = e$ for some $e$.

*Proof.* By compactness and Zorn's lemma there is a minimal nonempty closed subsemigroup $T$. Let $e \in T$. The set $T e$ is compact, hence closed, and it is a subsemigroup of $T$, since $(x e)(y e) = (x e y) e$. So $T e = T$, and $T' = \{x \in T : x e = e\}$ is nonempty. It is closed and a subsemigroup, since $(x y) e = x (y e) = e$. So $T' = T$, and $e e = e$. $\square$

::: mathlib
`exists_idempotent_of_compact_t2_of_continuous_mul_left` · `Mathlib.Topology.Algebra.Semigroup`

For a nonempty semigroup `M` with a compact Hausdorff topology and `∀ r, Continuous fun x ↦ x * r`, the statement `∃ m, m * m = m`. Hindman's file applies it to `Ultrafilter M`.

<?decl exists_idempotent_of_compact_t2_of_continuous_mul_left?>
:::

**Theorem (Sums inside a large set).** Let $U$ be an ultrafilter on a semigroup $M$ with $U + U = U$, and let $A \in U$. Then there is a sequence $a$ in $M$ with $FS(a) \subseteq A$.

*Proof.* For $B \subseteq M$ and $m \in M$ write $B - m = \{m' : m + m' \in B\}$. For $B \in U$ put $B^\star = \{m \in B : B - m \in U\}$. Idempotence says that $\{m : B - m \in U\} \in U$, so $B^\star \in U$.

*Step 1.* If $B \in U$ and $m \in B^\star$, then $B^\star - m \in U$. Indeed, $B^\star - m$ is the set of $m'$ with $m + m' \in B$ and $B - (m + m') \in U$. The first set is $B - m \in U$. For the second, note $B - (m + m') = (B - m) - m'$ by associativity, and idempotence for the set $B - m \in U$ gives $\{m' : (B - m) - m' \in U\} \in U$. The intersection of two sets in $U$ is in $U$.

*Step 2.* Put $B_0 = A$. Given $B_n \in U$, choose $a_n \in B_n^\star$, which is possible since $B_n^\star \in U$ is nonempty, and put $B_{n+1} = B_n^\star \cap (B_n^\star - a_n)$. By Step 1, $B_{n+1} \in U$, and $B_{n+1} \subseteq B_n$.

*Step 3.* Each sum $a_{n_1} + \dots + a_{n_k}$ with $n_1 < \dots < n_k$ lies in $B_{n_1}$. For $k = 1$, $a_{n_1} \in B_{n_1}^\star \subseteq B_{n_1}$. For $k > 1$, the sum $t = a_{n_2} + \dots + a_{n_k}$ lies in $B_{n_2}$ by induction, and $B_{n_2} \subseteq B_{n_1 + 1} \subseteq B_{n_1}^\star - a_{n_1}$. So $a_{n_1} + t \in B_{n_1}^\star \subseteq B_{n_1}$.

Since every $B_n \subseteq A$, all finite sums lie in $A$. $\square$

::: mathlib
`Hindman.exists_FS_of_large` · `Mathlib.Combinatorics.Hindman`

For `U : Ultrafilter M` with `U + U = U` and `s₀ ∈ U`, the statement `∃ a, ∀ m, FS a m → m ∈ s₀`. The multiplicative form is `Hindman.exists_FP_of_large`. The lemma `Hindman.exists_idempotent_ultrafilter_le_FS` gives, for any sequence `a`, an idempotent ultrafilter that contains `FS a`.

<?decl Hindman.exists_FS_of_large?>
:::

**Theorem (Hindman).** Let $M$ be a nonempty semigroup, and colour $M$ with finitely many colours. Then some colour class contains $FS(a)$ for some sequence $a$.

*Proof.* The space $\beta M$ is a nonempty compact Hausdorff semigroup with continuous maps $U \mapsto U + V$. The lemma of Ellis and Numakura gives an idempotent $U$. The colour classes are finitely many sets with union $M \in U$. An ultrafilter that contains a finite union contains one of the sets. So some colour class $A$ is in $U$, and the previous theorem applies to $A$. $\square$

::: mathlib
`Hindman.exists_FS_of_finite_cover` · `Mathlib.Combinatorics.Hindman`

For `[Nonempty M]` and a finite family `s : Set (Set M)` with `⊤ ⊆ ⋃₀ s`, the statement `∃ c ∈ s, ∃ a, ∀ m, FS a m → m ∈ c`. The variant `Hindman.FS_partition_regular` refines a given set `FS a`.

<?decl Hindman.exists_FS_of_finite_cover?>
:::

For $M = \mathbb{N}$ with $0$ the theorem has a trivial instance: the constant sequence $0$ has $FS = \{0\}$, which lies in the colour class of $0$. The content is in a semigroup with no idempotent element, such as the positive integers under addition.

### Examples

**Example (Two letters).** For $|\alpha| = 2$ and $r$ colours, $n = r$ suffices. Take $\alpha = \{0, 1\}$ and the $r + 1$ words $p_j = 1^j 0^{r-j}$ for $j = 0, \dots, r$. Two of them, $p_j$ and $p_{j'}$ with $j < j'$, have the same colour by pigeonhole. The word $1^j \ast^{j'-j} 0^{r-j'}$ is a line with the two points $p_j$ and $p_{j'}$.

**Example (A van der Waerden number).** Colour $1, \dots, 8$ as $R R B B R R B B$. A progression $x, x + d, x + 2d$ in the red set $\{1, 2, 5, 6\}$ needs $d \in \{1, 3, 4, 5\}$, the differences of red pairs, and each case leaves the set. The blue set is the red set shifted by $2$. So the least $W$ for which each red and blue colouring of $\{1, \dots, W\}$ has a monochromatic progression of length 3 is more than 8. Its value is 9.

### The library around it

The file `HalesJewett` also has combinatorial subspaces: `Subspace η α ι` has a word `ι → α ⊕ η` in which each variable of `η` occurs. The theorem `Subspace.exists_mono_in_high_dimension` finds a monochromatic subspace of any finite dimension $|\eta|$. It follows from the line version over the alphabet $\alpha^\eta$, through `Line.toSubspace`.

The file `Hindman` proves both the additive and the multiplicative forms, by `to_additive`. Chapter 6 treats Roth's theorem, a density form of van der Waerden's theorem for progressions of length 3.

### Exercises

1. (A) List the lines of $\{0,1\}^3$ and check the count $3^3 - 2^3 = 19$.
2. (A) Show that the colouring $RRBBRRBB$ of $\{1, \dots, 8\}$ cannot be extended to $9$ without a monochromatic progression of length 3. Then show that each colouring of $\{1, \dots, 9\}$ has one.
3. (A) Show that $FS(a)$ for $a_n = 2^n$ is the set of positive integers.
4. (B) Prove the finite form of van der Waerden's theorem from the infinite form, using Rado selection as in Section 1.
5. (B) Check that the sum of ultrafilters is an ultrafilter and that it is associative.
6. (B) Show that a principal ultrafilter at $m$ is idempotent if and only if $m + m = m$. Deduce that each idempotent of $\beta \mathbb{N}_{>0}$ is not principal.
7. (C) Prove Gallai's theorem: each finite colouring of $\mathbb{N}^2$ has a monochromatic square $\{(b_1 + a i, b_2 + a j) : 0 \le i, j < k\}$ for each $k$. Hint: `exists_mono_homothetic_copy`.
8. (C) Show that each finite colouring of $\mathbb{N}_{>0}$ has a sequence $a$ with $FS(a)$ in one colour and $a_{n+1} > a_0 + \dots + a_n$ for each $n$. Hint: by Exercise 6 the idempotent is not principal, so it contains each cofinite set. Use this in Step 2.

### Notes and history

Van der Waerden proved his theorem in 1927. Hales and Jewett proved their theorem in 1963. The proof by colour focusing is in the book *Ramsey Theory* of Graham, Rothschild and Spencer. Hindman proved his theorem in 1974. The proof with idempotent ultrafilters is due to Galvin and Glazer, and the existence of idempotents in compact semigroups is due to Ellis (1958) and Numakura (1952).

The files `HalesJewett` and `Hindman` list David Wärn as author.

### Reference

<?reference?>
