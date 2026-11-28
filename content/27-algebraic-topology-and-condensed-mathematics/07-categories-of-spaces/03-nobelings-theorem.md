---
title: Nöbeling's theorem
kind: theory
modules:
  - Mathlib.Topology.Category.Profinite.Nobeling.Basic
  - Mathlib.Topology.Category.Profinite.Nobeling.Span
  - Mathlib.Topology.Category.Profinite.Nobeling.ZeroLimit
  - Mathlib.Topology.Category.Profinite.Nobeling.Successor
  - Mathlib.Topology.Category.Profinite.Nobeling.Induction
explains:
  E3: [LocallyConstant.freeOfProfinite, Profinite.NobelingProof.Products, Profinite.NobelingProof.Products.isGood, Profinite.NobelingProof.GoodProducts, Profinite.NobelingProof.GoodProducts.span, Profinite.NobelingProof.GoodProducts.linearIndependent, Profinite.NobelingProof.succ_exact]
  E2: [Profinite.NobelingProof.e, Profinite.NobelingProof.Products.eval, Profinite.NobelingProof.GoodProducts.span_iff_products, Profinite.NobelingProof.GoodProducts.spanFin, Profinite.NobelingProof.spanCone_isLimit, Profinite.NobelingProof.Proj, Profinite.NobelingProof.π, Profinite.NobelingProof.πs, Profinite.NobelingProof.ord, Profinite.NobelingProof.term, Profinite.NobelingProof.contained, Profinite.NobelingProof.P, Profinite.NobelingProof.GoodProducts.P0, Profinite.NobelingProof.GoodProducts.Plimit, Profinite.NobelingProof.GoodProducts.linearIndependentAux, Profinite.NobelingProof.GoodProducts.linearIndependentSingleton, Profinite.NobelingProof.GoodProducts.union, Profinite.NobelingProof.Products.limitOrdinal, Profinite.NobelingProof.C0, Profinite.NobelingProof.C1, Profinite.NobelingProof.C', Profinite.NobelingProof.SwapTrue, Profinite.NobelingProof.Linear_CC', Profinite.NobelingProof.succ_mono, Profinite.NobelingProof.GoodProducts.MaxProducts, Profinite.NobelingProof.GoodProducts.sum_equiv, Profinite.NobelingProof.Products.max_eq_eval, Profinite.NobelingProof.GoodProducts.maxTail_isGood, Profinite.NobelingProof.GoodProducts.Basis, Profinite.NobelingProof.Nobeling_aux, Profinite.Nobeling.ι, Profinite.Nobeling.isClosedEmbedding]
  E1: auto
families: []
requires: [V07, V13.C05, V13.C06, V31.C02, V31.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Nöbeling's theorem

### Overview

Let $S$ be a profinite set. A continuous map $S \to \mathbb{Z}$ is the same as a locally constant map, because $\mathbb{Z}$ is discrete. These maps form an abelian group $\mathrm{LC}(S, \mathbb{Z})$ under pointwise addition. The theorem of Nöbeling says that this group is free.

For a finite $S$ the group is $\mathbb{Z}^S$, and the claim is clear. For an infinite $S$ it is not clear at all. The group of all maps $\mathbb{N} \to \mathbb{Z}$ is not free, by a theorem of Baer. The group of bounded maps $\mathbb{N} \to \mathbb{Z}$ is $\mathrm{LC}(\beta\mathbb{N}, \mathbb{Z})$, and the theorem says that it is free.

In condensed mathematics the theorem computes duals. A free group has the dual $\prod_I \mathbb{Z}$, and in the lecture notes of Clausen and Scholze the dual of $\mathrm{LC}(S, \mathbb{Z})$ is the underlying group of the solid free module on $S$. So the theorem shows that this group is a product of copies of $\mathbb{Z}$.

The proof is a transfinite induction. It embeds $S$ into a product $\{0,1\}^I$, puts a well order on $I$, and writes an explicit basis of products of coordinate functions, the *good products*. The spanning part is a finite argument. The independence part is the induction, with a zero step, a limit step and a successor step. The successor step uses a left exact sequence that compares $S$ with two smaller closed sets.

### Definitions

Throughout, $I$ is a type with a well order $<$, and $C \subseteq \{0,1\}^I$ is closed. Points of $C$ are maps $x : I \to \{0, 1\}$. Write $\mathrm{LC}(C)$ for $\mathrm{LC}(C, \mathbb{Z})$.

**Definition (Coordinate function).** For $i \in I$, the map $e_i \in \mathrm{LC}(C)$ is $e_i(x) = 1$ if $x_i = 1$ and $e_i(x) = 0$ if $x_i = 0$. It is locally constant because the coordinate $x \mapsto x_i$ is continuous to a discrete space.

**Definition (Product).** A *product* is a strictly decreasing finite list $l = [i_1, \dots, i_r]$ in $I$, with $i_1 > \dots > i_r$. Its *evaluation* is $\mathrm{ev}(l) = e_{i_1} \cdots e_{i_r} \in \mathrm{LC}(C)$. The empty list evaluates to the constant $1$. Products are ordered lexicographically: compare the first entries, and if they are equal compare the rests, with the empty list smallest.

**Definition (Good product).** A product $l$ is *good* for $C$ if $\mathrm{ev}(l)$ is not in the span of the evaluations of the products $m < l$.

**Definition (Projection).** For a set $J \subseteq I$, the map $\mathrm{Proj}_J : \{0,1\}^I \to \{0,1\}^I$ keeps the coordinates in $J$ and sets the others to $0$. Write $\pi_J(C)$ for the image of $C$. For an ordinal $o$, write $\pi_{<o}$ for $\pi_J$ with $J = \{i \mid \mathrm{ord}(i) < o\}$, where $\mathrm{ord}(i)$ is the order type of $\{j \mid j < i\}$.

**Definition (Contained).** The set $C$ is *contained in* $o$ if every $x \in C$ has $x_i = 0$ for all $i$ with $\mathrm{ord}(i) \ge o$. The statement $P(o)$ says: for every closed $C$ contained in $o$, the evaluations of the good products of $C$ are linearly independent.

### Theorems and proofs

**Lemma (Products are well ordered).** The lexicographic order on products is a well order.

*Proof.* It is a linear order. Assume an infinite strictly descending chain $l_0 > l_1 > \cdots$. Each $l_k$ is greater than some product, so it is not empty. The heads of a descending chain do not increase, since $m < l$ with $m$ not empty gives $\mathrm{head}(m) \le \mathrm{head}(l)$. A non increasing sequence in a well order is eventually constant, with value $a_0$. From that index, remove the heads. Lexicographic order compares the rests when the heads are equal, so the rests form an infinite descending chain, and their heads are $< a_0$ because the lists are strictly decreasing. Repeat the argument with this chain. This gives $a_0 > a_1 > a_2 > \cdots$ in $I$, which a well order does not allow. $\square$

**Theorem (The good products span).** The evaluations of the good products of $C$ span $\mathrm{LC}(C)$.

*Proof.* First, every product $l$ is in the span of the good ones. Use induction on $l$ along the well order of the lemma. If $l$ is good, there is nothing to prove. If not, $\mathrm{ev}(l)$ is a combination of evaluations of products $m < l$, and each of these is in the span of the good products by induction.

So it suffices to show that all products span. For a finite $s \subseteq I$, the set $\pi_s(C)$ is finite, and $C$ is the limit of the sets $\pi_s(C)$ over all finite $s$. A locally constant map on a cofiltered limit of finite sets factors through one stage, by Section 2. So $f \in \mathrm{LC}(C)$ has the form $f = g \circ \mathrm{Proj}_s$ for a finite $s$ and $g : \pi_s(C) \to \mathbb{Z}$. The map $g$ is a finite combination of indicators $\delta_y$ of points $y \in \pi_s(C)$, and on $C$,

$$\delta_y \circ \mathrm{Proj}_s = \prod_{i \in s,\, y_i = 1} e_i \prod_{i \in s,\, y_i = 0} (1 - e_i).$$

Expand the product. Since $e_i^2 = e_i$ and the $e_i$ commute, each term is $\pm$ a product of distinct $e_i$, which is $\pm \mathrm{ev}(l)$ for the list $l$ of these indices in decreasing order. So $f$ is in the span of the products. $\square$

**Theorem (Zero step).** $P(0)$ holds.

*Proof.* If $C$ is contained in $0$, every coordinate of every point is $0$. So $C = \emptyset$ or $C = \{0\}$. If $C = \emptyset$, then $\mathrm{LC}(C) = 0$, and no product is good, since every element of the zero module is in every span. The empty family is independent. If $C = \{0\}$, then $\mathrm{LC}(C) = \mathbb{Z}$, $\mathrm{ev}([\,]) = 1$, and $e_i = 0$ for all $i$. So $[\,]$ is good, since $1 \notin \mathrm{span}(\emptyset) = 0$. A non empty product $l$ has $\mathrm{ev}(l) = 0$, so it is not good. The family $\{1\}$ is independent in $\mathbb{Z}$. $\square$

**Theorem (Limit step).** Let $o$ be a limit ordinal and assume $P(o')$ for all $o' < o$. Then $P(o)$ holds.

*Proof.* Let $C$ be closed and contained in $o$. For $o' < o$, the restriction along $\pi_{<o'}$ is the injective linear map $\pi^\ast : \mathrm{LC}(\pi_{<o'}(C)) \to \mathrm{LC}(C)$, $g \mapsto g \circ \mathrm{Proj}_{<o'}$. It is injective because $\mathrm{Proj}_{<o'}$ maps $C$ onto $\pi_{<o'}(C)$.

Let $l$ be good for $C$. Its entries have $\mathrm{ord} < o$, because a product with an entry $i$ of larger order has $e_i = 0$ on $C$ and is not good. As $o$ is a limit, $o' = \mathrm{ord}(\mathrm{head}(l)) + 1 < o$; for the empty product take $o' = 0$. Every product $m < l$ has head at most the head of $l$, so all its entries have $\mathrm{ord} < o'$. For such products, $\mathrm{ev}_C(m) = \pi^\ast(\mathrm{ev}_{\pi_{<o'}(C)}(m))$. Since $\pi^\ast$ is injective, a linear relation among these evaluations holds on $C$ if and only if it holds on $\pi_{<o'}(C)$. So $l$ is good for $C$ if and only if it is good for $\pi_{<o'}(C)$.

Hence the set of evaluations of the good products of $C$ is the union over $o' < o$ of the images under $\pi^\ast$ of the evaluations of the good products of $\pi_{<o'}(C)$. Each of these sets is independent, by $P(o')$ applied to the closed set $\pi_{<o'}(C)$, which is contained in $o'$, and by the injectivity of $\pi^\ast$. They increase with $o'$. A linear relation uses finitely many elements, and they all lie in one set of the chain. So the union is independent. $\square$

**Theorem (Left exact sequence).** Let $C$ be closed and contained in $o + 1$, and let $t \in I$ have $\mathrm{ord}(t) = o$. Put $C_0 = \{x \in C \mid x_t = 0\}$, $C_1 = \{x \in C \mid x_t = 1\}$, $\bar C = \pi_{<o}(C)$ and $C' = C_0 \cap \pi_{<o}(C_1)$. Let $\sigma$ set the coordinate $t$ to $1$. Then the sequence

$$0 \to \mathrm{LC}(\bar C) \xrightarrow{\pi^\ast} \mathrm{LC}(C) \xrightarrow{\delta} \mathrm{LC}(C'), \qquad \delta(f)(x) = f(\sigma(x)) - f(x)$$

is exact.

*Proof.* On $C$ the map $\mathrm{Proj}_{<o}$ only sets the coordinate $t$ to $0$, so $\bar C = C_0 \cup \pi_{<o}(C_1)$. For $x \in C'$, write $x = \mathrm{Proj}_{<o}(y)$ with $y \in C_1$; then $\sigma(x) = y \in C$. So $\delta$ is well defined. The map $\pi^\ast$ is injective, as in the limit step. For $g \in \mathrm{LC}(\bar C)$ and $x \in C'$, $\mathrm{Proj}_{<o}(\sigma(x)) = x = \mathrm{Proj}_{<o}(x)$, so $\delta(\pi^\ast g)(x) = g(x) - g(x) = 0$.

Let $\delta(f) = 0$. Define $g$ on $\bar C$ by $g = f$ on $C_0$ and $g(y) = f(\sigma(y))$ on $\pi_{<o}(C_1)$. The two definitions agree on the overlap $C'$ because $\delta(f) = 0$. Both pieces are closed and $g$ is locally constant on each, so $g$ is locally constant. For $x \in C_0$, $g(\mathrm{Proj}_{<o}(x)) = g(x) = f(x)$. For $x \in C_1$, $g(\mathrm{Proj}_{<o}(x)) = f(\sigma(\mathrm{Proj}_{<o}(x))) = f(x)$. So $f = \pi^\ast g$. $\square$

**Theorem (Successor step).** If $P(o)$ holds, then $P(o + 1)$ holds.

*Proof.* Keep the notation of the previous theorem. The sets $\bar C$ and $C'$ are closed and contained in $o$, so $P(o)$ applies to them. A good product of $C$ has entries of order at most $o$. It either has all entries of order $< o$, or it has head $t$.

For a product $l$ with entries of order $< o$, $\mathrm{ev}_C(l) = \pi^\ast(\mathrm{ev}_{\bar C}(l))$, and the argument of the limit step shows that $l$ is good for $C$ if and only if it is good for $\bar C$.

For a product $l = t :: l'$ and $x \in C'$, $e_t(\sigma x) = 1$, $e_t(x) = 0$, and $\mathrm{ev}(l')(\sigma x) = \mathrm{ev}(l')(x)$, since the entries of $l'$ differ from $t$. So $\delta(\mathrm{ev}_C(t :: l')) = \mathrm{ev}_{C'}(l')$.

Next, if $t :: l'$ is good for $C$, then $l'$ is good for $C'$. If not, $\mathrm{ev}_{C'}(l') = \sum_{m < l'} c_m \mathrm{ev}_{C'}(m)$. Each $t :: m$ is a product with $t :: m < t :: l'$. The element $\varphi = \mathrm{ev}_C(t :: l') - \sum c_m \mathrm{ev}_C(t :: m)$ has $\delta(\varphi) = 0$, so $\varphi = \pi^\ast(g)$ by exactness. By the spanning theorem for $\bar C$, $g$ is a combination of evaluations of products with entries of order $< o$, and these products are smaller than $t :: l'$. So $\mathrm{ev}_C(t :: l')$ is a combination of evaluations of smaller products, against its goodness.

Now take a relation $\sum_l a_l \mathrm{ev}_C(l) = 0$ over good products of $C$. Apply $\delta$. The terms with entries of order $< o$ vanish, since they lie in the image of $\pi^\ast$. The rest gives $\sum a_{t :: l'} \mathrm{ev}_{C'}(l') = 0$, a relation among good products of $C'$, with distinct $l'$ for distinct $l$. By $P(o)$ for $C'$, these coefficients are $0$. The remaining relation is $\pi^\ast\bigl(\sum a_l \mathrm{ev}_{\bar C}(l)\bigr) = 0$. Injectivity of $\pi^\ast$ and $P(o)$ for $\bar C$ give $a_l = 0$. $\square$

**Theorem (Nöbeling).** For a profinite set $S$, the group $\mathrm{LC}(S, \mathbb{Z})$ is free.

*Proof.* Let $I$ be the set of clopen subsets of $S$, with a well order, which exists by the well ordering theorem. The map $\iota : S \to \{0,1\}^I$, $\iota(s)_U = 1$ if $s \in U$, is continuous. It is injective because clopen sets separate points. A continuous injection from a compact space to a Hausdorff space is a closed embedding, so $\mathrm{LC}(S) \cong \mathrm{LC}(C)$ for the closed set $C = \iota(S)$. By transfinite induction with the three steps, $P(o)$ holds for every ordinal $o$ up to the order type of $I$. Every $C$ is contained in that order type. So the good products of $C$ are independent, and by the spanning theorem they form a basis. $\square$

### Examples

**Example (Three points).** Let $I = \{0, 1\}$ with $0 < 1$, and $C = \{a, b, c\}$ with $a = (0,0)$, $b = (1,0)$, $c = (1,1)$, written as $(x_0, x_1)$. On $(a, b, c)$: $1 = (1,1,1)$, $e_0 = (0,1,1)$, $e_1 = (0,0,1)$, and $e_1 e_0 = (0,0,1)$. The products in order are $[\,] < [0] < [1] < [1, 0]$. The product $[\,]$ is good. $[0]$ is good because $e_0$ is not a multiple of $1$. $[1]$ is good because every combination of $1$ and $e_0$ has equal values at $b$ and $c$. $[1, 0]$ is not good because $e_1 e_0 = e_1$. The matrix with rows $1, e_0, e_1$ is upper triangular with ones on the diagonal, so $\{1, e_0, e_1\}$ is a basis of $\mathrm{LC}(C) = \mathbb{Z}^3$, as the theorem says.

**Example (The full square).** For $C = \{0,1\}^2$, all four products are good. The functions $1, e_0, e_1$ have the form $\alpha + \beta x_0 + \gamma x_1$, while $e_1 e_0$ is the indicator of $(1,1)$, which is not of this form. The four functions form a basis of $\mathbb{Z}^4$, with the inverse given by the inclusion and exclusion formula $\delta_{(0,0)} = 1 - e_0 - e_1 + e_1 e_0$.

**Example (Convergent sequences).** For $S = \mathbb{N} \cup \{\infty\}$, a locally constant $f$ is constant on a neighbourhood of $\infty$. So $f - f(\infty) \cdot 1$ has finite support in $\mathbb{N}$, and $f = f(\infty) \cdot 1 + \sum_n (f(n) - f(\infty)) \delta_n$, a finite sum. The family $\{1\} \cup \{\delta_n\}_n$ is a basis: evaluation at $\infty$ and then at each $n$ recovers the coefficients.

### The library around it

::: mathlib
`LocallyConstant.freeOfProfinite` · `Mathlib.Topology.Category.Profinite.Nobeling.Induction`

The instance `Module.Free ℤ (LocallyConstant S ℤ)` for `S : Profinite`. It comes from `Profinite.NobelingProof.Nobeling_aux`, through the closed embedding `Profinite.Nobeling.ι` into `{C : Set S // IsClopen C} → Bool`, whose property is `Profinite.Nobeling.isClosedEmbedding`. The well order on the clopen sets is chosen with `exists_wellFoundedLT`.

<?decl LocallyConstant.freeOfProfinite?>
:::

::: mathlib
`Profinite.NobelingProof.Products` · `Mathlib.Topology.Category.Profinite.Nobeling.Basic`

The subtype `{l : List I // l.IsChain (· > ·)}` with the lexicographic order, and the instance `WellFoundedLT` of the lemma above. The evaluation is `Profinite.NobelingProof.Products.eval`, the product of the `Profinite.NobelingProof.e C i`. The coordinate sets in the source are `Bool`, not $\{0,1\}$.

<?decl Profinite.NobelingProof.Products?>
:::

::: mathlib
`Profinite.NobelingProof.Products.isGood` · `Mathlib.Topology.Category.Profinite.Nobeling.Basic`

The predicate `l.eval C ∉ Submodule.span ℤ ((Products.eval C) '' {m | m < l})`. The set of good products is `Profinite.NobelingProof.GoodProducts C`, and `Profinite.NobelingProof.GoodProducts.span_iff_products` is the reduction to all products in the spanning proof.

<?decl Profinite.NobelingProof.Products.isGood?>
:::

::: mathlib
`Profinite.NobelingProof.GoodProducts.span` · `Mathlib.Topology.Category.Profinite.Nobeling.Span`

The statement that the span of the good products is everything, for a closed `C`. The finite case is `Profinite.NobelingProof.GoodProducts.spanFin`, and the passage to the limit uses `Profinite.NobelingProof.spanCone_isLimit`, which writes a compact `C` as the limit of its finite projections.

<?decl Profinite.NobelingProof.GoodProducts.span?>
:::

::: mathlib
`Profinite.NobelingProof.GoodProducts.linearIndependent` · `Mathlib.Topology.Category.Profinite.Nobeling.Induction`

Linear independence for a closed `C`, from `Profinite.NobelingProof.GoodProducts.linearIndependentAux`, which proves the predicate `Profinite.NobelingProof.P` for all ordinals. The three steps are `GoodProducts.P0`, `GoodProducts.Plimit` and the successor case in `Nobeling.Successor`. The predicate `P o` carries the hypothesis `o ≤ Ordinal.type (· < ·)`, so the element `Profinite.NobelingProof.term I ho` of order `o` exists in the successor case. The basis itself is `Profinite.NobelingProof.GoodProducts.Basis`.

<?decl Profinite.NobelingProof.GoodProducts.linearIndependent?>
:::

::: mathlib
`Profinite.NobelingProof.succ_exact` · `Mathlib.Topology.Category.Profinite.Nobeling.Successor`

Exactness in the middle of the left exact sequence, with `Profinite.NobelingProof.succ_mono` for the injectivity. The sets are `C0`, `C1` and `C'`, the map $\sigma$ is `SwapTrue`, and $\delta$ is `Linear_CC'`. The splitting of the good products is `GoodProducts.sum_equiv`, between the good products of $\bar C$ and `GoodProducts.MaxProducts`, which are the ones with head $t$. The identity $\delta(\mathrm{ev}(t :: l')) = \mathrm{ev}(l')$ is `Products.max_eq_eval`, and `GoodProducts.maxTail_isGood` is the step on the tail.

<?decl Profinite.NobelingProof.succ_exact?>
:::

Common errors of a learner:

- A good product depends on $C$. The same list can be good for $\bar C$ and not good for $C'$.
- The order on products compares the largest index first, because the lists decrease. So $[1] < [1, 0]$ but $[1, 0] < [2]$.
- The source proves only left exactness of the sequence. The docstring warns that "is a basis" in the paper must be read as "is linearly independent" in the induction; the spanning part is separate.
- `LocallyConstant S ℤ` is not `C(S, ℤ)` as a type, although the two agree for a discrete target.

### Exercises

1. (A) For $C = \{(0,0), (0,1), (1,1)\}$ in $\{0,1\}^{\{0,1\}}$, find the good products and check that they form a basis. *Hint:* compute $e_0$, $e_1$ and $e_1 e_0$ as vectors.
2. (A) Show that for any $C$ the empty product is good if and only if $C$ is not empty.
3. (A) Show that the products in $I = \{0, 1, 2\}$ number $8$, and list them in lexicographic order. *Hint:* a decreasing list is a subset.
4. (B) Let $C \subseteq \{0,1\}^I$ be finite. Show that the number of good products equals $|C|$. *Hint:* $\mathrm{LC}(C) = \mathbb{Z}^C$ has rank $|C|$.
5. (B) Show that the group of bounded sequences $\mathbb{N} \to \mathbb{Z}$ is $\mathrm{LC}(\beta\mathbb{N}, \mathbb{Z})$. *Hint:* a bounded sequence takes finitely many values, and each fibre extends to a clopen subset of $\beta\mathbb{N}$.
6. (B) Describe the good products of the Cantor set $\{0,1\}^{\mathbb{N}}$, with the usual order on $\mathbb{N}$. *Hint:* the coordinates are independent, so every product is good.
7. (C) Prove that a subgroup of $\mathrm{LC}(S, \mathbb{Z})$ is free, using only the theorem and a general fact about free abelian groups. *Hint:* subgroups of free abelian groups are free (Volume 7).

### Notes and history

Nöbeling proved the theorem in 1968. For $\beta\mathbb{N}$ it says that the group of bounded integer sequences is free, a result of Specker. The proof in Mathlib follows Theorem 5.4 of the lecture notes of Scholze on condensed mathematics from 2019, as the source states, and the table in `Nobeling.Successor` translates the notation of the notes to the Lean names.

The Mathlib Author of `Nobeling.Basic`, `Nobeling.Span`, `Nobeling.ZeroLimit`, `Nobeling.Successor` and `Nobeling.Induction` is Dagur Asgeirsson.

### Reference

<?reference?>
