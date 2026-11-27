---
title: Doubling, Ruzsa and Plünnecke
kind: theory
modules:
  - Mathlib.Combinatorics.Additive.DoublingConst
  - Mathlib.Combinatorics.Additive.PluenneckeRuzsa
  - Mathlib.Combinatorics.Additive.RuzsaCovering
  - Mathlib.Combinatorics.Additive.Energy
explains:
  E3: [Finset.addConst, Finset.subConst, Finset.ruzsa_triangle_inequality_sub_sub_sub, Finset.ruzsa_triangle_inequality_sub_add_add, Finset.ruzsa_covering_add, Finset.pluennecke_petridis_inequality_add, Finset.pluennecke_ruzsa_inequality_nsmul_add, Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add, Finset.addEnergy]
  E2: [Finset.mulConst, Finset.divConst, Finset.cast_addConst, Finset.cast_subConst, Finset.addConst_le_card, Finset.subConst_le_card, Finset.addConst_le_inv_dens, Finset.addConst_empty_left, Finset.addConst_empty_right, Finset.subConst_le_addConst_sq, Finset.addConst_le_subConst_sq, Finset.ruzsa_triangle_inequality_add_add_add, Finset.ruzsa_triangle_inequality_sub_add_sub, Finset.ruzsa_triangle_inequality_add_sub_sub, Finset.ruzsa_triangle_inequality_div_div_div, Finset.ruzsa_triangle_inequality_mul_mul_mul, Finset.pluennecke_petridis_inequality_mul, Finset.pluennecke_ruzsa_inequality_pow_mul, Finset.pluennecke_ruzsa_inequality_pow_div_pow_mul, Finset.pluennecke_ruzsa_inequality_nsmul_sub, Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_sub, Finset.ruzsa_covering_mul, Set.ruzsa_covering_add, Finset.mulEnergy, Finset.le_addEnergy, Finset.le_addEnergy_self, Finset.addEnergy_comm, Finset.addEnergy_mono, Finset.addEnergy_pos, Finset.addEnergy_eq_card_filter, Finset.addEnergy_eq_sum_sq, Finset.addEnergy_eq_sum_sq', Finset.card_sq_le_card_mul_addEnergy, Finset.le_card_add_mul_addEnergy]
  E1: auto
families: []
requires: [V03.C03, V03.C06, V05.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Doubling, Ruzsa and Plünnecke

### Overview

The previous section gave lower bounds for the size of a sumset. This section studies the sets for which the sumset is small. If $A$ is a finite set in an abelian group and $|A + A| \le K|A|$ for a constant $K$, then $A$ is said to have small doubling. An arithmetic progression has doubling less than $2$, and a subgroup has doubling $1$. The theorem of Freiman says that, in the integers, the sets of small doubling are exactly the large subsets of generalised arithmetic progressions. That theorem is deep, and it is not in the index of this edition. This section proves the elementary tools that come before it and that are used in each proof of it.

There are three tools. The Ruzsa triangle inequality is a triangle inequality for the quantity $\log(|A - B|^2/(|A||B|))$, which behaves like a distance between finite sets. The Ruzsa covering lemma says that a set $A$ with $|A + B|$ small is covered by a few translates of $B - B$. The Plünnecke-Ruzsa inequality says that small doubling of $A$ gives small size for all the iterated sums $nA - mA$. Its modern proof, due to Petridis in 2012, takes one page, and this section gives it in full. The section ends with the additive energy, which counts the solutions of $a + b = a' + b'$.

### Definitions

In this section, $G$ is an abelian group and all sets are finite subsets of $G$. For $n \ge 1$, $nA = A + \dots + A$ is the sum of $n$ copies of $A$, and $0A = \{0\}$. This is not the dilate $\{na : a \in A\}$.

**Definition (Doubling and difference constants).** For non-empty $A$ and any $B$, the doubling constant of $A$ and $B$ is $\sigma[A, B] = |A + B|/|A|$, and the difference constant is $\delta[A, B] = |A - B|/|A|$. Write $\sigma[A] = \sigma[A, A]$ and $\delta[A] = \delta[A, A]$.

Since $A + B$ contains a translate of $A$ when $B$ is non-empty, $\sigma[A, B] \ge 1$. Also $|A + B| \le |A||B|$, so $\sigma[A, B] \le |B|$.

::: mathlib
`Finset.addConst` · `Mathlib.Combinatorics.Additive.DoublingConst`

`A.addConst B : ℚ≥0` is `#(A + B) / #A`, with the notation `σ[A, B]` in the scope `Combinatorics.Additive`, and `σ[A]` for `σ[A, A]`. The cast to a field is `Finset.cast_addConst`. The value for `A = ∅` is $0$ by division by zero, `Finset.addConst_empty_left`. The bound by the size of the second set is `Finset.addConst_le_card`, and in a finite group `Finset.addConst_le_inv_dens` gives $\sigma[A, B] \le 1/\operatorname{dens}(A)$. The multiplicative form is `Finset.mulConst`, with the notation `σₘ[A, B]`.

<?decl Finset.addConst?>
:::

::: mathlib
`Finset.subConst` · `Mathlib.Combinatorics.Additive.DoublingConst`

`A.subConst B : ℚ≥0` is `#(A - B) / #A`, with the notation `δ[A, B]`. The multiplicative form is `Finset.divConst`, with `δₘ[A, B]`. The two inequalities `Finset.subConst_le_addConst_sq`, $\delta[A] \le \sigma[A]^2$, and `Finset.addConst_le_subConst_sq`, $\sigma[A] \le \delta[A]^2$, are proved below. The second one needs a commutative group.

<?decl Finset.subConst?>
:::

**Definition (Additive energy).** The additive energy of $A$ and $B$ is the number of quadruples
$$E(A, B) = \#\{(a, a', b, b') \in A \times A \times B \times B : a + b = a' + b'\}.$$
For $x \in G$, let $r(x) = \#\{(a, b) \in A \times B : a + b = x\}$. A quadruple is a pair of representations of the same $x$, so $E(A, B) = \sum_x r(x)^2$.

::: mathlib
`Finset.addEnergy` · `Mathlib.Combinatorics.Additive.Energy`

`s.addEnergy t : ℕ` is the card of the finset of `((a, a'), (b, b'))` in `(s ×ˢ s) ×ˢ t ×ˢ t` with `a + b = a' + b'`, with the notation `E[s, t]`. The unfolding is `Finset.addEnergy_eq_card_filter`, and the sum of squares is `Finset.addEnergy_eq_sum_sq'` over `s + t`, or `Finset.addEnergy_eq_sum_sq` over a finite type. The trivial bounds are `Finset.le_addEnergy`, $|s||t| \le E[s, t]$, and `Finset.le_addEnergy_self`. The energy is symmetric, `Finset.addEnergy_comm`, and monotone, `Finset.addEnergy_mono`. The definition needs only an addition, not a group.

<?decl Finset.addEnergy?>
:::

### Theorems and proofs

**Theorem (Ruzsa triangle inequality).** For finite sets $A, B, C$ in a group,
$$|A - C|\,|B| \le |A - B|\,|C - B|.$$

*Proof.* For each $x \in A - C$, choose one representation $x = a_x - c_x$ with $a_x \in A$ and $c_x \in C$. Define a map
$$\phi : (A - C) \times B \to (A - B) \times (C - B), \qquad \phi(x, b) = (a_x - b,\ c_x - b).$$
The map is injective. Let $\phi(x, b) = (u, v)$. Then $u - v = a_x - c_x = x$, so $x$ is determined by $(u, v)$. Then $a_x$ is determined, and $b = a_x - u$. The sizes of the two sides of an injection give the inequality. $\square$

The proof does not use commutativity, if $a - b$ is read as $a b^{-1}$. If the sets are non-empty, divide by $|A||B||C|$ and take logarithms. The quantity $d(A, B) = \log\big(|A - B| / \sqrt{|A||B|}\big)$ then satisfies $d(A, C) \le d(A, B) + d(B, C)$. It is the Ruzsa distance. It is symmetric and non-negative, but $d(A, A) = 0$ only when $A$ is a coset of a subgroup.

::: mathlib
`Finset.ruzsa_triangle_inequality_sub_sub_sub` · `Mathlib.Combinatorics.Additive.PluenneckeRuzsa`

`ruzsa_triangle_inequality_sub_sub_sub (A B C : Finset G) : #(A - C) * #B ≤ #(A - B) * #(C - B)`, in an additive group. The proof in Mathlib is a double counting with `Finset.card_mul_le_card_mul`, not an injection, but the idea is the same. The multiplicative form `Finset.ruzsa_triangle_inequality_div_div_div` comes first in the source. The file has all the variants with sums and differences on the two sides, each obtained by replacing a set by its negative. The names list the operations in the three sumsets of the statement: `Finset.ruzsa_triangle_inequality_sub_add_sub`, `Finset.ruzsa_triangle_inequality_add_sub_sub` and others.

<?decl Finset.ruzsa_triangle_inequality_sub_sub_sub?>
:::

**Corollary.** For finite sets $A, B, C$ in a group, $|A - C|\,|B| \le |A + B|\,|C + B|$. In particular, $\delta[A] \le \sigma[A]^2$ for non-empty $A$.

*Proof.* Apply the triangle inequality to $A$, $-B$ and $C$, and use $|-B| = |B|$ and $A - (-B) = A + B$. For the second claim, take $A = B = C$: $|A - A|\,|A| \le |A + A|^2$. Divide by $|A|^2$. $\square$

::: mathlib
`Finset.ruzsa_triangle_inequality_sub_add_add` · `Mathlib.Combinatorics.Additive.PluenneckeRuzsa`

`ruzsa_triangle_inequality_sub_add_add (A B C : Finset G) : #(A - C) * #B ≤ #(A + B) * #(C + B)`. The form with three sums, `Finset.ruzsa_triangle_inequality_add_add_add`, $|A + C||B| \le |A + B||B + C|$, is not a direct consequence of the triangle inequality. It needs the Plünnecke-Petridis lemma below, and Mathlib proves it after that lemma.

<?decl Finset.ruzsa_triangle_inequality_sub_add_add?>
:::

**Theorem (Ruzsa covering lemma).** Let $A, B$ be finite sets in a group with $B$ non-empty and $|A + B| \le K |B|$. Then there is $F \subseteq A$ with $|F| \le K$ and $A \subseteq F + (B - B)$.

*Proof.* Among the subsets $F \subseteq A$ such that the translates $f + B$ for $f \in F$ are pairwise disjoint, choose a maximal one. The empty set is such a subset, so the choice is possible. The translates are disjoint and contained in $A + B$, so
$$|F|\,|B| = |F + B| \le |A + B| \le K|B|,$$
and $|F| \le K$. Let $a \in A$. If $a \in F$, then $a = a + b - b \in F + (B - B)$ for any $b \in B$. If $a \notin F$, then $F \cup \{a\}$ is not admissible by maximality, so $a + B$ meets $f + B$ for some $f \in F$. Then $a + b = f + b'$ with $b, b' \in B$, and $a = f + (b' - b) \in F + (B - B)$. $\square$

::: mathlib
`Finset.ruzsa_covering_add` · `Mathlib.Combinatorics.Additive.RuzsaCovering`

`ruzsa_covering_add (hB : B.Nonempty) (hK : #(A + B) ≤ K * #B) : ∃ F ⊆ A, #F ≤ K ∧ A ⊆ F + (B - B)`, with `K : ℝ`. The proof is the maximality argument above, with `Finset.exists_maximal` on the finset of admissible subsets. The form for finite sets is `Set.ruzsa_covering_add`, with `Nat.card`, and the multiplicative form is `Finset.ruzsa_covering_mul`.

<?decl Finset.ruzsa_covering_add?>
:::

**Theorem (Plünnecke-Petridis lemma).** Let $A, B$ be finite sets in an abelian group with $A$ non-empty. Suppose that
$$\frac{|A + B|}{|A|} \le \frac{|A' + B|}{|A'|} \quad \text{for each non-empty } A' \subseteq A,$$
and let $K = |A + B|/|A|$. Then $|C + A + B| \le K\,|C + A|$ for each finite set $C$.

*Proof.* The hypothesis says $|A' + B| \ge K|A'|$ for each $A' \subseteq A$, also for $A' = \emptyset$. Use induction on $|C|$. If $C = \emptyset$, both sides are $0$. Let $C = C' \cup \{c\}$ with $c \notin C'$, and suppose the claim for $C'$. Define
$$Y = \{x \in A : c + x + B \subseteq C' + A + B\}, \qquad Z = \{x \in A : c + x \in C' + A\}.$$
Then $Z \subseteq Y$: if $c + x \in C' + A$, then $c + x + B \subseteq C' + A + B$.

First, $C + A + B$ is the union of $C' + A + B$ and $(c + A + B) \setminus (c + Y + B)$, because $c + Y + B \subseteq C' + A + B$. Thus
$$|C + A + B| \le |C' + A + B| + |A + B| - |Y + B|.$$
Second, $C + A$ is the disjoint union of $C' + A$ and $c + (A \setminus Z)$, by the definition of $Z$. Thus
$$|C + A| = |C' + A| + |A| - |Z|.$$
Now use the induction hypothesis, $|A + B| = K|A|$, and $|Y + B| \ge K|Y| \ge K|Z|$:
$$|C + A + B| \le K|C' + A| + K|A| - K|Z| = K|C + A|. \quad \square$$

::: mathlib
`Finset.pluennecke_petridis_inequality_add` · `Mathlib.Combinatorics.Additive.PluenneckeRuzsa`

`pluennecke_petridis_inequality_add (C : Finset G) (hA : ∀ A' ⊆ A, #(A + B) * #A' ≤ #(A' + B) * #A) : #(C + A + B) * #A ≤ #(A + B) * #(C + A)`. The hypothesis and the conclusion are multiplied out, so no division and no non-emptiness hypothesis appear. The proof is the induction above with `Finset.induction_on`. The multiplicative form is `Finset.pluennecke_petridis_inequality_mul`.

<?decl Finset.pluennecke_petridis_inequality_add?>
:::

**Theorem (Plünnecke-Ruzsa inequality).** Let $A, B$ be finite sets in an abelian group with $A$ non-empty, and let $K = |A + B|/|A|$. Then for all $m, n \ge 0$,
$$|nB| \le K^n |A|, \qquad |mB - nB| \le K^{m+n} |A|.$$

*Proof.* Choose a non-empty $X \subseteq A$ for which $|X + B|/|X|$ is least, and let $K' = |X + B|/|X|$. Then $K' \le K$, and $X$ satisfies the hypothesis of the Plünnecke-Petridis lemma. Apply the lemma with $C = (n - 1)B$, for $n \ge 1$:
$$|X + nB| = |(n-1)B + X + B| \le K'\,|X + (n-1)B|.$$
By induction on $n$, $|X + nB| \le K'^n |X|$. A translate of $nB$ is inside $X + nB$, so
$$|nB| \le |X + nB| \le K'^n |X| \le K^n |A|.$$
For the second claim, apply the corollary of the triangle inequality with the sets $mB$, $X$ and $nB$:
$$|mB - nB|\,|X| \le |mB + X|\,|nB + X| \le K'^m |X| \cdot K'^n |X|.$$
Divide by $|X|$, and use $K' \le K$ and $|X| \le |A|$. $\square$

The case $A = B$ gives the form that is used most: if $|A + A| \le K|A|$, then $|mA - nA| \le K^{m+n}|A|$. In particular, $\sigma[A] \le \delta[A]^2$ follows from the same argument with $B = -A$.

::: mathlib
`Finset.pluennecke_ruzsa_inequality_nsmul_add` · `Mathlib.Combinatorics.Additive.PluenneckeRuzsa`

`pluennecke_ruzsa_inequality_nsmul_add (hA : A.Nonempty) (B : Finset G) (n : ℕ) : #(n • B) ≤ (#(A + B) / #A) ^ n * #A`, as an inequality in `ℚ≥0`, in a commutative additive group. Here `n • B` is the iterated sumset, not the dilate, by the pointwise instances. The multiplicative form `Finset.pluennecke_ruzsa_inequality_pow_mul` has `B ^ n`. The variant with a difference constant in the hypothesis is `Finset.pluennecke_ruzsa_inequality_nsmul_sub`.

<?decl Finset.pluennecke_ruzsa_inequality_nsmul_add?>
:::

::: mathlib
`Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add` · `Mathlib.Combinatorics.Additive.PluenneckeRuzsa`

`pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add (hA : A.Nonempty) (B : Finset G) (m n : ℕ) : #(m • B - n • B) ≤ (#(A + B) / #A) ^ (m + n) * #A`. The name lists the iterated difference `m • B - n • B` and then the sumset `A + B` of the hypothesis. With `A - B` in place of `A + B`, the form is `Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_sub`. In the source, the general statement is the multiplicative `Finset.pluennecke_ruzsa_inequality_pow_div_pow_mul`, and the others follow from it.

<?decl Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add?>
:::

**Proposition (Energy and sumsets).** For finite non-empty $A, B$, $|A|^2 |B|^2 \le |A + B|\, E(A, B)$, and $E(A, B) \le |A|^2|B|$.

*Proof.* The function $r$ has support $A + B$ and $\sum_x r(x) = |A||B|$. By the Cauchy-Schwarz inequality,
$$|A|^2|B|^2 = \Big(\sum_{x \in A + B} r(x)\Big)^2 \le |A + B| \sum_x r(x)^2 = |A + B|\,E(A, B).$$
For the upper bound, a quadruple $(a, a', b, b')$ with $a + b = a' + b'$ is determined by $a$, $a'$ and $b$. $\square$

Thus small doubling gives large energy: if $|A + A| \le K|A|$, then $E(A, A) \ge |A|^3 / K$. The converse is false. The set $A = \{1, \dots, n\} \cup \{2^n, \dots, 2^{2n}\}$ has energy at least $2n^3/3$, from the interval, but $|A + A| \ge n^2/2$, from the powers of $2$. The theorem of Balog, Szemerédi and Gowers gives a partial converse: a set with energy at least $|A|^3/K$ has a subset $A'$ of size at least $|A|/K^C$ with $|A' + A'| \le K^C|A'|$, for an absolute constant $C$. The index of this edition has no declaration for it.

::: mathlib
`Finset.le_card_add_mul_addEnergy` · `Mathlib.Combinatorics.Additive.Energy`

`le_card_add_mul_addEnergy (s t : Finset α) : #s ^ 2 * #t ^ 2 ≤ #(s + t) * E[s, t]`. A more general form is `Finset.card_sq_le_card_mul_addEnergy`, which bounds the square of the number of pairs with sum in a set `u` by `#u * E[s, t]`. Both are proved with the Cauchy-Schwarz inequality for finite sums.

<?decl Finset.le_card_add_mul_addEnergy?>
:::

### Examples

**Example (Doubling of an arithmetic progression).** Let $P = \{a, a + d, \dots, a + (k-1)d\}$ with $d \neq 0$ in $\mathbb{Z}$. Then $P + P$ is the progression of length $2k - 1$ from $2a$ with difference $d$, and $\sigma[P] = (2k - 1)/k < 2$. Also $nP$ has $n(k - 1) + 1$ elements, much less than the bound $\sigma[P]^n |P|$ of Plünnecke-Ruzsa. The bound is exponential in $n$, but the true growth is linear for a progression.

**Example (A set with large doubling).** Let $A = \{1, 2, 4, \dots, 2^{k-1}\}$. A sum $2^i + 2^j$ with $i < j$ has two binary digits $1$, and a sum $2^i + 2^i$ has one, so different pairs give different sums. Thus $|A + A| = \binom{k}{2} + k$, and $\sigma[A] = (k + 1)/2$. This is the largest possible value for a set of size $k$.

**Example (Covering).** Let $A = \{0, 1, \dots, 99\}$ and $B = \{0, 1, \dots, 9\}$ in $\mathbb{Z}$. Then $|A + B| = 109 \le 10.9 \cdot |B|$. The covering lemma gives $F \subseteq A$ with $|F| \le 10$ and $A \subseteq F + \{-9, \dots, 9\}$. The maximal disjoint family $F = \{0, 10, 20, \dots, 90\}$ from the proof has $10$ elements and works.

**Example (Energy of a subgroup).** For a subgroup $H$, each $x \in H$ has $r(x) = |H|$ representations as $h + h'$, so $E(H, H) = |H| \cdot |H|^2 = |H|^3$. This is the upper bound of the proposition, attained.

### The library around it

`Mathlib.Combinatorics.Additive.DoublingConst` has the doubling and difference constants. `Mathlib.Combinatorics.Additive.PluenneckeRuzsa` has the triangle inequalities, the Plünnecke-Petridis lemma and the Plünnecke-Ruzsa inequalities, in the order of this section. `Mathlib.Combinatorics.Additive.RuzsaCovering` has the covering lemma, and `Mathlib.Combinatorics.Additive.Energy` has the additive energy. The folder has more on sets of small doubling: `Mathlib.Combinatorics.Additive.SmallTripling` shows that small tripling gives small growth of all iterated products in a non-abelian group, `Mathlib.Combinatorics.Additive.VerySmallDoubling` studies sets with doubling less than $3/2$, which are close to cosets, and `Mathlib.Combinatorics.Additive.ApproximateSubgroup` defines approximate subgroups. Freiman homomorphisms are in `Mathlib.Combinatorics.Additive.FreimanHom`. The index of this edition has no declaration for the theorem of Freiman and no declaration for the polynomial Freiman-Ruzsa theorem of Gowers, Green, Manners and Tao, whose formal proof is in a separate project.

Common errors of a learner:

- `n • B` for a finset `B` is the iterated sumset $B + \dots + B$ in the pointwise scope, not the dilate $\{nb : b \in B\}$. The dilate is the image of `B` under `(n • ·)`.
- `σ[A, B]` is a value in `ℚ≥0`. A statement with real numbers needs a cast, and `Finset.cast_addConst` gives the cast to any division semiring.
- The Plünnecke-Ruzsa inequalities in Mathlib need `AddCommGroup`. The triangle inequalities and the covering lemma do not need commutativity.
- The doubling constant divides by the size of the first set: `σ[A, B] = #(A + B) / #A`. In the covering lemma, the hypothesis divides by the size of `B`.

### Exercises

1. (A) Compute $\sigma[A]$ and $\delta[A]$ for $A = \{0, 1, 3\}$ in $\mathbb{Z}$, and check $\delta[A] \le \sigma[A]^2$.
2. (A) Show that $\sigma[A] = 1$ for a finite non-empty $A$ in an abelian group if and only if $A$ is a coset of a subgroup.
3. (A) Show that the Ruzsa distance $d(A, B)$ is symmetric and that $d(A, B) \ge 0$. Hint: $|A - B| \ge \max(|A|, |B|)$.
4. (A) Show that $E(A, B) \le \min(|A|^2|B|, |A||B|^2)$.
5. (B) Let $A \subseteq \mathbb{Z}$ with $|A + A| \le K|A|$. Show $|A - A| \le K^2 |A|$ in two ways: with the triangle inequality and with Plünnecke-Ruzsa.
6. (B) Let $A$ in an abelian group satisfy $|A + A| \le K|A|$. Show that $2A - A$ is covered by at most $K^4$ translates of $A - A$. Hint: apply the covering lemma to $2A - A$ and $A$.
7. (B) Give an example of $A$ and $B$ in $\mathbb{Z}$ with $|A + B|$ small and $|B + B|$ large. Explain why the Plünnecke-Ruzsa inequality bounds $|nB|$ by $K^n |A|$ and not by $K^n|B|$.
8. (B) Prove $|A + C|\,|B| \le |A + B|\,|B + C|$ in an abelian group from the Plünnecke-Petridis lemma. Hint: choose a minimising $X \subseteq B$ for $B + A$ and apply the lemma with $C$.
9. (C) Let $A \subseteq \mathbb{F}_2^n$ with $|A + A| \le K|A|$. Show that the subgroup generated by $A$ has at most $K^2 2^{K^4} |A|$ elements. Hint: by Exercise 6, $2A - A \subseteq X + (A - A)$ with $|X| \le K^4$. Deduce that the subgroup is contained in $\langle X \rangle + (A - A)$. This is a theorem of Ruzsa.
10. (C) Find the step in the proof of Exercise 8 that needs commutativity. Explain why the Plünnecke-Petridis lemma is stated with $C + A + B$ and not with $A + C + B$.

### Notes and history

Plünnecke proved his inequality in 1970 with a theory of commutative graphs and Menger's theorem. Ruzsa simplified the proof in 1989, introduced the triangle inequality and the covering lemma, and used them in 1994 for a new proof of the theorem of Freiman of 1964. Petridis found the short proof of this section in 2012, when he was a graduate student. Balog and Szemerédi proved their theorem in 1994, and Gowers gave polynomial bounds in 1998 in his proof of the theorem of Szemerédi for progressions of length four. The polynomial Freiman-Ruzsa conjecture for $\mathbb{F}_2^n$ was proved by Gowers, Green, Manners and Tao in 2023, and its proof was formalised in Lean within a few weeks. The headers list Yaël Dillies for `Mathlib.Combinatorics.Additive.DoublingConst` and `Mathlib.Combinatorics.Additive.RuzsaCovering`, Yaël Dillies and George Shakan for `Mathlib.Combinatorics.Additive.PluenneckeRuzsa`, and Yaël Dillies and Ella Yu for `Mathlib.Combinatorics.Additive.Energy`.

### Reference

<?reference?>
