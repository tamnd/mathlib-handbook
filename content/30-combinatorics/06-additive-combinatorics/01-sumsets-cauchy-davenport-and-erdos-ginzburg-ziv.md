---
title: Sumsets, Cauchy-Davenport and Erdős-Ginzburg-Ziv
kind: theory
modules:
  - Mathlib.Combinatorics.Additive.CauchyDavenport
  - Mathlib.Combinatorics.Additive.ETransform
  - Mathlib.Combinatorics.Additive.ErdosGinzburgZiv
explains:
  E3: [ZMod.cauchy_davenport, cauchy_davenport_add_of_linearOrder_isCancelAdd, cauchy_davenport_minOrder_add, Finset.addDysonETransform, Int.erdos_ginzburg_ziv, ZMod.erdos_ginzburg_ziv]
  E2: [cauchy_davenport_mul_of_linearOrder_isCancelMul, cauchy_davenport_minOrder_mul, cauchy_davenport_of_isAddTorsionFree, cauchy_davenport_of_isMulTorsionFree, Finset.mulDysonETransform, Finset.addDysonETransform.subset, Finset.addDysonETransform.card, Finset.addDysonETransform_idem, Finset.addDysonETransform.vadd_finset_snd_subset_fst, Finset.addETransformLeft, Finset.addETransformRight, Finset.addETransformLeft.fst_add_snd_subset, Finset.addETransformRight.fst_add_snd_subset, Finset.AddETransform.card, Finset.mulETransformLeft, Finset.mulETransformRight, Int.erdos_ginzburg_ziv_multiset, ZMod.erdos_ginzburg_ziv_multiset]
  E1: auto
families: []
requires: [V03.C03, V03.C06, V05.C04, V12.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Sumsets, Cauchy-Davenport and Erdős-Ginzburg-Ziv

### Overview

Additive combinatorics studies the additive structure of finite sets. The basic object is the sumset $A + B = \{a + b : a \in A, b \in B\}$ of two finite sets in an abelian group. The basic question is how small $A + B$ can be, given the sizes of $A$ and $B$, and what the sets look like when $A + B$ is small.

In the integers, the answer to the first question is easy: $|A + B| \ge |A| + |B| - 1$, with equality for two arithmetic progressions with the same difference. In a finite group, the sumset cannot be larger than the group, and a subgroup $H$ has $H + H = H$. The theorem of Cauchy and Davenport says that in $\mathbb{Z}/p\mathbb{Z}$, with $p$ prime, these are the only obstacles: $|A + B| \ge \min(p, |A| + |B| - 1)$. The proof uses the e-transform of Dyson, which changes the pair $(A, B)$ so that the sum of the sizes stays the same and the sumset does not grow.

The theorem of Erdős, Ginzburg and Ziv is a first application. Among any $2n - 1$ integers, there are $n$ whose sum is divisible by $n$. The prime case follows from Cauchy-Davenport, and the general case follows from the prime case by induction on the number of prime factors.

### Definitions

**Definition (Sumset).** Let $G$ be an abelian group and $A, B \subseteq G$ finite. The sumset is $A + B = \{a + b : a \in A,\ b \in B\}$. For $x \in G$, the translate is $x + A = \{x + a : a \in A\}$, and $-A = \{-a : a \in A\}$. The difference set is $A - B = A + (-B)$.

A translate has the same size as $A$, and $(x + A) + B = x + (A + B)$. Thus a translation of $A$ or $B$ changes nothing in the questions of this section.

Mathlib writes the sumset of two finsets as `s + t`, with the pointwise instances of Volume 5, and the translate as `x +ᵥ s`. The multiplicative form is `s * t` and `x • s`. The declarations of this section exist in both forms, and the multiplicative one is the primary one in the source.

**Definition (Dyson e-transform).** Let $A, B \subseteq G$ be finite and $e \in G$. The Dyson e-transform of $(A, B)$ at $e$ is the pair
$$A' = A \cup (e + B), \qquad B' = B \cap (-e + A).$$

**Lemma.** For the Dyson e-transform, $A' + B' \subseteq A + B$ and $|A'| + |B'| = |A| + |B|$.

*Proof.* Let $a' \in A'$ and $b' \in B'$. If $a' \in A$, then $a' + b' \in A + B$ because $b' \in B$. If $a' = e + b$ with $b \in B$, then $b' = -e + a$ with $a \in A$, so $a' + b' = a + b \in A + B$. For the sizes, translate $B'$ by $e$: $e + B' = (e + B) \cap A$. Thus
$$|A'| + |B'| = |A \cup (e + B)| + |A \cap (e + B)| = |A| + |e + B| = |A| + |B|. \quad \square$$

::: mathlib
`Finset.addDysonETransform` · `Mathlib.Combinatorics.Additive.ETransform`

`addDysonETransform e x` takes a pair `x : Finset α × Finset α` in a commutative group and returns `(x.1 ∪ e +ᵥ x.2, x.2 ∩ -e +ᵥ x.1)`. The two parts of the lemma are `Finset.addDysonETransform.subset` and `Finset.addDysonETransform.card`. The transform is idempotent, `Finset.addDysonETransform_idem`. For non-commutative groups, the file has the pair of transforms `Finset.mulETransformLeft` and `Finset.mulETransformRight`, which change `(s, t)` into `(s ∩ s • e, t ∪ e⁻¹ • t)` and `(s ∪ s • e, t ∩ e⁻¹ • t)`. Each of them can increase the sum of the sizes, but `Finset.MulETransform.card` says that the total over the two is constant, so one of the two does not decrease it.

<?decl Finset.addDysonETransform?>
:::

### Theorems and proofs

**Theorem (Sumsets in a linear order).** Let $A, B$ be non-empty finite sets of integers. Then $|A + B| \ge |A| + |B| - 1$.

*Proof.* Write $A = \{a_1 < \dots < a_k\}$ and $B = \{b_1 < \dots < b_l\}$. The $k + l - 1$ sums
$$a_1 + b_1 < a_2 + b_1 < \dots < a_k + b_1 < a_k + b_2 < \dots < a_k + b_l$$
are strictly increasing, so they are distinct elements of $A + B$. $\square$

The same proof works in each linearly ordered cancellative semigroup, because it uses only that addition is strictly monotone in each variable. The bound is sharp. For $A = \{0, 1, \dots, k - 1\}$ and $B = \{0, 1, \dots, l - 1\}$, the sumset is $\{0, \dots, k + l - 2\}$.

::: mathlib
`cauchy_davenport_add_of_linearOrder_isCancelAdd` · `Mathlib.Combinatorics.Additive.CauchyDavenport`

`cauchy_davenport_add_of_linearOrder_isCancelAdd (hs : s.Nonempty) (ht : t.Nonempty) : #s + #t - 1 ≤ #(s + t)`, in a type with a linear order, a cancellative addition and monotone addition on both sides. The Mathlib proof is shorter than the chain above. It shows that `s + {min t}` and `{max s} + t` meet in exactly one point, and counts their union. The multiplicative form is `cauchy_davenport_mul_of_linearOrder_isCancelMul`. For torsion-free groups, the same bound is `cauchy_davenport_of_isAddTorsionFree`.

<?decl cauchy_davenport_add_of_linearOrder_isCancelAdd?>
:::

**Theorem (Cauchy-Davenport).** Let $p$ be a prime and $A, B \subseteq \mathbb{Z}/p\mathbb{Z}$ non-empty. Then
$$|A + B| \ge \min(p, |A| + |B| - 1).$$

*Proof.* Use induction on $|B|$, for all $A$ at the same time. If $|B| = 1$, then $A + B$ is a translate of $A$, and $|A + B| = |A| = |A| + |B| - 1$.

Let $|B| \ge 2$. A translation of $B$ changes neither side, so suppose that $0 \in B$. Choose $b \in B$ with $b \neq 0$.

Suppose first that $e + B \subseteq A$ for each $e \in A$. Then $A + b \subseteq A$, and by induction $A + jb \subseteq A$ for each $j \ge 0$. The element $b$ generates $\mathbb{Z}/p\mathbb{Z}$, because the order of $b$ divides $p$ and is not $1$. Thus $A$ is the whole group, and $|A + B| = p$.

Otherwise, there is $e \in A$ with $e + B \not\subseteq A$. Let $(A', B')$ be the Dyson e-transform at $e$. Then $0 \in B'$, because $0 \in B$ and $-e + e = 0$ with $e \in A$. Thus $B'$ is non-empty. Also $B' \neq B$: there is $b_0 \in B$ with $e + b_0 \notin A$, and then $b_0 \notin -e + A$. Thus $|B'| < |B|$. By the induction hypothesis and the lemma,
$$|A + B| \ge |A' + B'| \ge \min(p, |A'| + |B'| - 1) = \min(p, |A| + |B| - 1). \quad \square$$

The bound is sharp. If $|A| + |B| - 1 \le p$, take two arithmetic progressions with the same difference. If $|A| + |B| - 1 > p$, then $|A + B| = p$: for each $x$, the sets $A$ and $x - B$ have more than $p$ elements together, so they meet, and $x \in A + B$.

::: mathlib
`ZMod.cauchy_davenport` · `Mathlib.Combinatorics.Additive.CauchyDavenport`

`ZMod.cauchy_davenport (hp : p.Prime) (hs : s.Nonempty) (ht : t.Nonempty) : min p (#s + #t - 1) ≤ #(s + t)`, for `s t : Finset (ZMod p)`. It is a corollary of the general theorem below, with the fact that the least order of a non-trivial element of `ZMod p` is $p$.

<?decl ZMod.cauchy_davenport?>
:::

**Theorem (Cauchy-Davenport in a group).** Let $G$ be a group, and let $m \in \mathbb{N} \cup \{\infty\}$ be the least order of an element $g \neq 1$ of $G$. For non-empty finite $A, B \subseteq G$, $|AB| \ge \min(m, |A| + |B| - 1)$.

The theorem is due to DeVos in 2016. The proof is an induction like the one above, with the pair of non-commutative e-transforms. It also gives the torsion-free case, where $m = \infty$.

::: mathlib
`cauchy_davenport_minOrder_add` · `Mathlib.Combinatorics.Additive.CauchyDavenport`

`cauchy_davenport_minOrder_add (hs : s.Nonempty) (ht : t.Nonempty) : min (AddMonoid.minOrder α) ↑(#s + #t - 1) ≤ #(s + t)`. The value `AddMonoid.minOrder α` is in `ℕ∞`, and it is `⊤` for a torsion-free group. The multiplicative form `cauchy_davenport_minOrder_mul` is the one the file proves first. The induction runs on a well-founded relation on pairs of finsets, which prefers first a smaller product set, then a larger sum of the sizes, then a smaller first set.

<?decl cauchy_davenport_minOrder_add?>
:::

**Theorem (Erdős-Ginzburg-Ziv).** Let $n \ge 1$, and let $a_1, \dots, a_{2n-1}$ be integers. There is a set $T \subseteq \{1, \dots, 2n - 1\}$ with $|T| = n$ such that $n$ divides $\sum_{i \in T} a_i$.

*Proof.* *The prime case.* Let $n = p$ be prime. Reduce the $a_i$ modulo $p$ and order the indices so that the residues $r_1 \le r_2 \le \dots \le r_{2p-1}$ in $\{0, \dots, p - 1\}$ increase. If $r_i = r_{i + p - 1}$ for some $i \le p$, then the $p$ residues $r_i, \dots, r_{i+p-1}$ are equal, and their sum is $p r_i \equiv 0$. Otherwise, $r_i \neq r_{i+p-1}$ for $i = 1, \dots, p - 1$. Let $A_i = \{r_i, r_{i+p-1}\}$, a set of size $2$ in $\mathbb{Z}/p\mathbb{Z}$. By Cauchy-Davenport and induction on $j$,
$$|A_1 + \dots + A_j| \ge \min(p, j + 1).$$
For $j = p - 1$, the sumset is all of $\mathbb{Z}/p\mathbb{Z}$. In particular, it contains $-r_{2p-1}$. Thus there are choices $c_i \in \{i, i + p - 1\}$ for $i = 1, \dots, p - 1$ with $\sum_i r_{c_i} \equiv -r_{2p-1}$. The indices $c_1, \dots, c_{p-1}$ and $2p - 1$ are distinct, because the $c_i$ lie in the disjoint pairs $\{i, i + p - 1\}$ and none of them is $2p - 1$. The set $T = \{c_1, \dots, c_{p-1}, 2p - 1\}$ has $p$ elements and sum divisible by $p$.

*From $m$ and $n$ to $mn$.* Suppose that the theorem holds for $m$ and for $n$. Let $2mn - 1$ integers be given. Choose $n$ of them with sum divisible by $n$, and remove them. Repeat while at least $2n - 1$ integers remain. After $k$ steps, $2mn - 1 - kn$ integers remain, and this is at least $2n - 1$ when $k \le 2m - 2$. Thus the process gives $2m - 1$ disjoint sets $T_1, \dots, T_{2m-1}$ of size $n$, with sums $n s_1, \dots, n s_{2m-1}$. Apply the theorem for $m$ to $s_1, \dots, s_{2m-1}$. There are $m$ of them with sum $m t$. The union of the corresponding $T_j$ has $mn$ elements and sum $n \cdot m t$.

Each $n \ge 1$ is a product of primes, so the two steps prove the theorem. The case $n = 1$ is clear. $\square$

The number $2n - 1$ is sharp: the $2n - 2$ integers $0, \dots, 0, 1, \dots, 1$, with $n - 1$ copies of each, have no $n$ with sum divisible by $n$. A sum of $n$ of them is $j$ with $1 \le j \le n - 1$.

::: mathlib
`Int.erdos_ginzburg_ziv` · `Mathlib.Combinatorics.Additive.ErdosGinzburgZiv`

`Int.erdos_ginzburg_ziv (a : ι → ℤ) (hs : 2 * n - 1 ≤ #s) : ∃ t ⊆ s, #t = n ∧ ↑n ∣ ∑ i ∈ t, a i`. The statement takes a finset `s` of indices and a family `a`, so repeated values are allowed. The form for a multiset of integers is `Int.erdos_ginzburg_ziv_multiset`. Mathlib proves the prime case with the theorem of Chevalley and Warning on the zeros of polynomials over a finite field, not with Cauchy-Davenport. It applies Chevalley-Warning to the two polynomials $\sum_i x_i^{p-1}$ and $\sum_i a_i x_i^{p-1}$ in $2p - 1$ variables.

<?decl Int.erdos_ginzburg_ziv?>
:::

::: mathlib
`ZMod.erdos_ginzburg_ziv` · `Mathlib.Combinatorics.Additive.ErdosGinzburgZiv`

`ZMod.erdos_ginzburg_ziv (a : ι → ZMod n) (hs : 2 * n - 1 ≤ #s) : ∃ t ⊆ s, #t = n ∧ ∑ i ∈ t, a i = 0`. It follows from the integer form by lifting the residues. The multiset form is `ZMod.erdos_ginzburg_ziv_multiset`.

<?decl ZMod.erdos_ginzburg_ziv?>
:::

### Examples

**Example (Small sumsets in $\mathbb{Z}/7$).** Let $A = \{0, 1, 2\}$ and $B = \{0, 3\}$ in $\mathbb{Z}/7\mathbb{Z}$. Then $A + B = \{0, 1, 2, 3, 4, 5\}$ has $6$ elements, more than the bound $\min(7, 4) = 4$. For $B = \{0, 1\}$, the sumset is $\{0, 1, 2, 3\}$, and the bound is attained. For $A = \{0, 1, 2, 3\}$ and $B = \{0, 2, 4, 6\}$, the bound is $\min(7, 7) = 7$, so $A + B$ is the whole group.

**Example (A Dyson e-transform).** In $\mathbb{Z}/7\mathbb{Z}$, let $A = \{0, 1\}$, $B = \{0, 3, 5\}$ and $e = 0$. Then $e + B \not\subseteq A$. The transform gives $A' = \{0, 1, 3, 5\}$ and $B' = B \cap A = \{0\}$. The sizes add to $5$ in both cases, and $A' + B' = A' \subseteq A + B = \{0, 1, 3, 4, 5, 6\}$.

**Example (Erdős-Ginzburg-Ziv for $n = 3$).** Among the five integers $1, 4, 2, 2, 7$, the residues mod $3$ are $1, 1, 2, 2, 1$. Three residues $1$ give $1 + 4 + 7 = 12$, divisible by $3$. Among $0, 0, 1, 1$, no three have sum divisible by $3$, so five integers are necessary.

**Example (Restricted sums).** The theorem of Dias da Silva and Hamidoune, the conjecture of Erdős and Heilbronn, says that the set $\{a + a' : a, a' \in A,\ a \neq a'\}$ in $\mathbb{Z}/p\mathbb{Z}$ has at least $\min(p, 2|A| - 3)$ elements. The proof needs the polynomial method and is not in the index of this edition. The example $A = \{0, 1, \dots, k - 1\}$ shows that the bound is sharp.

### The library around it

`Mathlib.Combinatorics.Additive.ETransform` has the e-transforms, and `Mathlib.Combinatorics.Additive.CauchyDavenport` uses them for the general theorem. `Mathlib.Combinatorics.Additive.ErdosGinzburgZiv` uses `Mathlib.FieldTheory.ChevalleyWarning`. The pointwise operations on finsets are in `Mathlib.Algebra.Group.Pointwise.Finset.Basic`, and the next section uses them for the doubling constant. The index of this edition has no declaration for the theorem of Vosper on the case of equality in Cauchy-Davenport, and no declaration for the theorem of Kneser on sumsets in general abelian groups.

Common errors of a learner:

- In Mathlib, `s + t` for two finsets needs `open Pointwise`. Without it, the instance is not found, and the error message does not mention pointwise operations.
- The bound `#s + #t - 1` uses natural subtraction. It is correct because `s` and `t` are non-empty, so `#s + #t ≥ 2`. A goal without the hypotheses of non-emptiness is false: for `s = ∅` the sumset is empty.
- The multiplicative form is the primary one. A search for `cauchy_davenport_minOrder_add` finds the generated statement, but the proof is at `cauchy_davenport_minOrder_mul`.

### Exercises

1. (A) Show that $|A + B| = |A| + |B| - 1$ for non-empty finite $A, B \subseteq \mathbb{Z}$ if $A$ and $B$ are arithmetic progressions with the same difference.
2. (A) Show that $|A + A| = 2|A| - 1$ for a finite $A \subseteq \mathbb{Z}$ with $|A| \ge 2$ only if $A$ is an arithmetic progression.
3. (A) In $\mathbb{Z}/8\mathbb{Z}$, find non-empty $A$ and $B$ with $|A + B| < \min(8, |A| + |B| - 1)$. Explain why this does not contradict the general theorem of DeVos.
4. (A) Show that the Dyson e-transform at $e$ of $(A, B)$ is $(A, B)$ itself when $e + B \subseteq A$.
5. (B) Deduce from Cauchy-Davenport that each element of $\mathbb{Z}/p\mathbb{Z}$ is a sum of two squares, for $p$ an odd prime. Hint: the set of squares has $(p + 1)/2$ elements.
6. (B) Let $A_1, \dots, A_k \subseteq \mathbb{Z}/p\mathbb{Z}$ be non-empty. Show $|A_1 + \dots + A_k| \ge \min(p, \sum_i |A_i| - k + 1)$.
7. (B) Show that among any $n$ integers there is a non-empty subset with sum divisible by $n$. Compare with Erdős-Ginzburg-Ziv.
8. (B) Let $A \subseteq \mathbb{Z}/p\mathbb{Z}$ with $|A| > p/2$. Show that $A + A$ is the whole group, with a direct argument and with Cauchy-Davenport.
9. (C) Give a full proof of the theorem of DeVos for an abelian group. Follow the proof for $\mathbb{Z}/p\mathbb{Z}$, and use that the element $b$ in the first case generates a subgroup of order at least $m$.
10. (C) Prove the prime case of Erdős-Ginzburg-Ziv with the theorem of Chevalley and Warning, as in Mathlib.

### Notes and history

Cauchy proved the theorem for $\mathbb{Z}/p\mathbb{Z}$ in 1813, to solve the equation $a x^2 + b y^2 + c \equiv 0 \pmod p$. Davenport rediscovered it in 1935, in work on the sums of sets of integers with positive density, and found the paper of Cauchy in 1947. The e-transform is due to Dyson, in a paper of 1945 on the density of sumsets. Erdős, Ginzburg and Ziv proved their theorem in 1961. It started zero-sum theory, which asks, for a finite abelian group $G$, for the least $k$ such that each sequence of $k$ elements has a zero-sum subsequence of a given kind. DeVos proved the general form for arbitrary groups in 2016. The headers list Yaël Dillies and Bhavik Mehta for `Mathlib.Combinatorics.Additive.CauchyDavenport`, and Yaël Dillies for `Mathlib.Combinatorics.Additive.ETransform` and `Mathlib.Combinatorics.Additive.ErdosGinzburgZiv`.

### Reference

<?reference?>
