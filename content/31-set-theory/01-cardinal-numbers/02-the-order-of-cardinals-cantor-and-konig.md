---
title: The order of cardinals, Cantor and König
kind: theory
modules:
  - Mathlib.SetTheory.Cardinal.Order
explains:
  E3: [Cardinal.le_def, Cardinal.lt_wf, Cardinal.cantor, Cardinal.sum_lt_prod, Cardinal.IsStrongLimit]
  E2: [Cardinal.mk_le_of_injective, Cardinal.mk_le_of_surjective, Cardinal.lift_mk_le', Cardinal.mk_set, Cardinal.commSemiring, Cardinal.sInf_empty, Cardinal.instSuccOrder, Cardinal.add_one_le_of_lt, Cardinal.le_sum, Cardinal.iSup_le_sum, Cardinal.prod_le_prod, Cardinal.IsStrongPrelimit, Cardinal.IsStrongLimit.isSuccLimit, nonempty_embedding_to_cardinal, WellOrderingRel, exists_wellFoundedLT]
  E1: auto
families: []
requires: [V01.C03, V04.C01, V04.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The order of cardinals, Cantor and König

### Overview

Section 1 defined $\#\alpha \le \#\beta$ by an embedding $\alpha \hookrightarrow \beta$ and showed that this order is linear. This section proves that it is a well-order, so each nonempty set of cardinals has a least element and each cardinal has a successor. Two strict inequalities then give the structure of the order above a cardinal. Cantor's theorem says $a < 2^a$, so no cardinal is largest. König's theorem says that a sum is less than a product when each term is less than the matching factor. Cantor's theorem is its special case with constant terms.

The section also treats suprema, which exist only for families indexed by a type of the same universe, the strong limit cardinals, and the well-ordering theorem. In Mathlib the well-ordering theorem comes after the cardinals, not before: each type embeds in the cardinals of its universe, and the order of the cardinals pulls back.

### Definitions

**Definition (Strict order).** $a < b$ means $a \le b$ and not $b \le a$. For types, $\#\alpha < \#\beta$ holds when $\alpha$ embeds in $\beta$ and $\beta$ does not embed in $\alpha$.

By Schröder-Bernstein, $a < b$ is the same as $a \le b$ and $a \ne b$.

**Definition (Successor).** The *successor* $\mathrm{succ}\,a$ of a cardinal $a$ is the least cardinal $b$ with $a < b$.

The definition needs two facts: some cardinal is above $a$ (Cantor's theorem below), and the set of such cardinals has a least element (well-foundedness below).

**Definition (Supremum).** For a set $S$ of cardinals that is bounded above, $\sup S$ is the least upper bound of $S$. For a family $(c_i)_{i \in \iota}$, $\sup_i c_i$ is the supremum of its range.

**Definition (Strong limit).** A cardinal $c$ is a *strong limit* when $c \ne 0$ and $2^x < c$ for each $x < c$.

### Theorems and proofs

**Theorem (Well-foundedness).** Each nonempty set $S$ of cardinals of a universe $u$ has a least element.

*Proof.* Index a family of types by the elements of $S$: put $\beta_c = c.\mathrm{out}$ for $c \in S$. The index type is nonempty. The theorem on a minimal injective member (Section 1) gives $c_0 \in S$ with an embedding $c_0.\mathrm{out} \hookrightarrow c.\mathrm{out}$ for each $c \in S$. Since $\#(c.\mathrm{out}) = c$, this says $c_0 \le c$ for each $c \in S$. $\square$

So the cardinals of each universe are well-ordered. Transfinite induction on cardinals is valid, and each cardinal has a successor once one cardinal above it is known. The empty set has no least element, and Mathlib sets $\inf \emptyset = 0$.

**Theorem (Cantor).** For each cardinal $a$, $a < 2^a$.

*Proof.* Let $a = \#\alpha$. A subset of $\alpha$ is a map $\alpha \to \mathrm{Prop}$, and classically $\mathrm{Prop}$ has two elements, so $2^a = \#\,\mathrm{Set}\,\alpha$. The map $x \mapsto \{x\}$ is injective, so $a \le 2^a$. Suppose $2^a \le a$, so there is an injective $f : \mathrm{Set}\,\alpha \to \alpha$. Put $D = \{ f(T) : T \subseteq \alpha,\ f(T) \notin T \}$ and $d = f(D)$. If $d \in D$, then $d = f(T)$ with $f(T) \notin T$. Injectivity gives $T = D$, so $d \notin D$. If $d \notin D$, then $T = D$ witnesses $d \in D$. Both cases are contradictory. $\square$

Volume 1, Chapter 3, Section 2 proves the same lemma on injective maps. Volume 3, Chapter 8 applies it to the real numbers.

**Corollary (No largest cardinal).** For each family $(c_i)_{i \in \iota}$ with $\iota$ in universe $u$ and each $c_i \in \mathrm{Cardinal}_u$, the sum $s = \sum_i c_i$ is an upper bound, and $2^s$ is a cardinal of universe $u$ above every $c_i$. In particular the cardinals of universe $u$ are not indexed by any type of universe $u$.

*Proof.* The map $x \mapsto \langle i, x\rangle$ embeds $c_i.\mathrm{out}$ in $\Sigma i, c_i.\mathrm{out}$, so $c_i \le s < 2^s$. If $c : \iota \to \mathrm{Cardinal}_u$ were surjective, the cardinal $2^s$ would be some $c_i$, and $c_i < 2^s$ would fail. $\square$

This is Cantor's paradox in Lean form. In ZFC it says that the cardinals form a proper class. In Lean it says that $\mathrm{Cardinal}_u$ is not *small* for universe $u$. A set $S$ of cardinals is bounded above if and only if it is small, that is equivalent to a type of universe $u$. One direction is the corollary. For the other, if $S \subseteq \{x : x \le b\}$, the cardinals below $b$ inject into the subsets of $b.\mathrm{out}$, by $x \mapsto$ the range of a chosen embedding.

**Proposition (Successor and plus one).** If $a < b$, then $a + 1 \le b$. Hence $a + 1 \le \mathrm{succ}\,a$, with equality for finite $a$.

*Proof.* Let $a = \#\alpha$, $b = \#\beta$ and let $f : \alpha \hookrightarrow \beta$. The map $f$ is not surjective, since a surjection $\alpha \to \beta$ gives $b \le a$. Pick $y \in \beta$ outside the range of $f$. Extend $f$ to $\alpha \oplus \mathrm{Unit}$ by $\star \mapsto y$. This map is injective, so $a + 1 \le b$. For $b = \mathrm{succ}\,a$ this gives $a + 1 \le \mathrm{succ}\,a$. For finite $a = n$, the cardinal $n + 1$ is above $n$, so $\mathrm{succ}\,n \le n + 1$. $\square$

For infinite $a$, Section 3 shows $a + 1 = a$, so $\mathrm{succ}\,a \ne a + 1$.

**Theorem (König).** Let $(f_i)_{i \in \iota}$ and $(g_i)_{i \in \iota}$ be families of cardinals with $f_i < g_i$ for each $i$. Then $\sum_i f_i < \prod_i g_i$.

*Proof.* Choose types $A_i$ and $B_i$ with $\#A_i = f_i$ and $\#B_i = g_i$. Then $\sum_i f_i = \#(\Sigma i, A_i)$ and $\prod_i g_i = \#(\Pi i, B_i)$. Since the order is total, it suffices to show that $\prod_i g_i \le \sum_i f_i$ fails.

Each $B_i$ is nonempty, since $0 \le f_i < g_i$. By the axiom of choice, $\Pi i, B_i$ is nonempty. Suppose that $F : \Pi i, B_i \hookrightarrow \Sigma i, A_i$ is an embedding. Since the domain is nonempty, $F$ has a left inverse $G : \Sigma i, A_i \to \Pi i, B_i$, with $G(F(x)) = x$, and $G$ is surjective.

Fix $i$. The map $A_i \to B_i$, $a \mapsto G(\langle i, a\rangle)(i)$, is not surjective. Otherwise $\#B_i \le \#A_i$, which contradicts $f_i < g_i$. Choose $C_i \in B_i$ outside its range. This gives an element $C \in \Pi i, B_i$. Since $G$ is surjective, $C = G(\langle i, a\rangle)$ for some $i$ and some $a \in A_i$. Evaluate at $i$: $C_i = G(\langle i, a\rangle)(i)$. This puts $C_i$ in the range of the map for $i$, a contradiction. $\square$

The proof is a diagonal argument: coordinate $i$ of $C$ avoids the part of $\Sigma i, A_i$ over $i$. Cantor's theorem is the case $\iota = \alpha$, $f_i = 1$, $g_i = 2$: then $\sum_i 1 = \#\alpha$ and $\prod_i 2 = 2^{\#\alpha}$.

**Proposition (Strong limits are limits).** A strong limit $c$ is a successor limit: $c \ne 0$, and $\mathrm{succ}\,x < c$ for each $x < c$.

*Proof.* Let $x < c$. By Cantor, $x < 2^x$, so $\mathrm{succ}\,x \le 2^x$. Since $c$ is a strong limit, $2^x < c$. $\square$

**Theorem (Well-ordering).** Each type $\alpha$ of universe $u$ has a well-order.

*Proof.* First, there is an embedding $\alpha \hookrightarrow \mathrm{Cardinal}_u$. By comparability, otherwise there is an embedding $h : \mathrm{Cardinal}_u \hookrightarrow \alpha$. Since $\mathrm{Cardinal}_u$ is nonempty, $h$ has a surjective left inverse $g : \alpha \to \mathrm{Cardinal}_u$. This contradicts the corollary above, with $\iota = \alpha$. Now take an embedding $e : \alpha \hookrightarrow \mathrm{Cardinal}_u$ and put $x \prec y$ when $e(x) < e(y)$. This relation is a strict linear order, since $e$ is injective. A nonempty $T \subseteq \alpha$ has an element $x$ with $e(x)$ least in $e[T]$, and $x$ is least for $\prec$. $\square$

The axiom of choice enters through Zorn's lemma in Section 1 and through the left inverse. Zermelo's well-ordering theorem is thus a consequence of the theory of cardinals.

### Examples

**Example (Sums and products over the natural numbers).** Take $\iota = \mathbb{N}$, $f_n = n$ and $g_n = n + 1$. Then $f_n < g_n$ for each $n$. The sum $\sum_n n$ is the cardinal of $\Sigma n, \mathrm{Fin}\,n$, which is infinite and countable, so it is $\aleph_0$ by Section 3. The factor for $n = 0$ is $1$, so the product $\prod_n (n+1)$ equals $\prod_{n \ge 1} (n+1)$. This lies between $\prod_{n \ge 1} 2 = 2^{\aleph_0}$ and $\prod_{n \ge 1} \aleph_0 = \aleph_0^{\aleph_0} = 2^{\aleph_0}$, so it equals $2^{\aleph_0}$. König's theorem gives $\aleph_0 < 2^{\aleph_0}$ again.

**Counterexample (Strict inequality in each term).** König's theorem fails with $\le$ in place of $<$. Take $\iota = \mathbb{N}$ and $f_n = g_n = 1$. Then $\sum_n 1 = \#\mathbb{N}$, while $\prod_n 1 = \#(\mathbb{N} \to \mathrm{Unit}) = 1$. So the sum is larger than the product. With $\le$ in each term, only $\sum_i f_i \le \sum_i g_i$ and $\prod_i f_i \le \prod_i g_i$ hold.

**Example (A junk supremum).** The set of all cardinals of universe $u$ is not bounded above. Mathlib still defines its supremum: $\sup \mathrm{Cardinal}_u = 0$, from the conditionally complete order built on a well-order. A statement such as $c \le \sup S$ is false here for $c = 1$. Each lemma on suprema in Mathlib has a hypothesis `BddAbove`.

### The library around it

::: mathlib
`Cardinal.le_def` · `Mathlib.SetTheory.Cardinal.Order`

`le_def (α β : Type u) : #α ≤ #β ↔ Nonempty (α ↪ β)`. The partial order instance `Cardinal.partialOrder` takes antisymmetry from `Function.Embedding.antisymm`. The most used forms are `Cardinal.mk_le_of_injective` and `Cardinal.mk_le_of_surjective`. For types of two universes, `Cardinal.lift_mk_le'` states `lift.{v} #α ≤ lift.{u} #β ↔ Nonempty (α ↪ β)`. The module also gives `Cardinal.commSemiring` and an instance of canonically ordered addition: $a \le b$ if and only if $b = a + c$ for some $c$.

<?decl Cardinal.le_def?>
:::

::: mathlib
`Cardinal.lt_wf` · `Mathlib.SetTheory.Cardinal.Order`

The instance `WellFoundedLT Cardinal.{u}`. The proof applies `Function.Embedding.min_injective` to the cardinals that are not accessible. From it Mathlib builds `ConditionallyCompleteLinearOrderBot Cardinal` and the `SuccOrder` instance `Cardinal.instSuccOrder`. The junk values follow: `Cardinal.sInf_empty` gives `sInf ∅ = 0`, and the supremum of an unbounded set is `0`. The lemma `Cardinal.add_one_le_of_lt` is the proposition on successor and plus one.

<?decl Cardinal.lt_wf?>
:::

::: mathlib
`Cardinal.cantor` · `Mathlib.SetTheory.Cardinal.Order`

`cantor (a : Cardinal.{u}) : a < 2 ^ a`. The proof rewrites with `Cardinal.mk_set : #(Set α) = 2 ^ #α`, embeds by `singleton`, and concludes by `Function.cantor_injective`. It also gives the instance `NoMaxOrder Cardinal`.

<?decl Cardinal.cantor?>
:::

::: mathlib
`Cardinal.bddAbove_iff_small` · `Mathlib.SetTheory.Cardinal.Basic`

`bddAbove_iff_small {s : Set Cardinal.{u}} : BddAbove s ↔ Small.{u} s`. The upper bound in the proof is a `sum`, as in the corollary above. For a family indexed by `ι : Type u`, `Cardinal.le_sum` and `Cardinal.iSup_le_sum` give `f i ≤ sum f` and `iSup f ≤ sum f`.

<?decl Cardinal.bddAbove_iff_small?>
:::

::: mathlib
`Cardinal.sum_lt_prod` · `Mathlib.SetTheory.Cardinal.Order`

`sum_lt_prod {ι} (f g : ι → Cardinal) (H : ∀ i, f i < g i) : sum f < prod g`. The proof is the one above: `invFun` of the embedding, a choice of `C`, and evaluation at `i`. The weak forms are `Cardinal.prod_le_prod` and `Cardinal.sum_le_sum`.

<?decl Cardinal.sum_lt_prod?>
:::

::: mathlib
`Cardinal.IsStrongLimit` · `Mathlib.SetTheory.Cardinal.Order`

A structure with the fields `ne_zero : c ≠ 0` and `isStrongPrelimit : IsStrongPrelimit c`, where `Cardinal.IsStrongPrelimit c` is `∀ x < c, 2 ^ x < c`. The lemma `Cardinal.IsStrongLimit.isSuccLimit` is the proposition above. The docstring notes that `ℵ₀` is a strong limit by this definition.

<?decl Cardinal.IsStrongLimit?>
:::

::: mathlib
`exists_wellFoundedLT` · `Mathlib.SetTheory.Cardinal.Order`

`exists_wellFoundedLT (α : Type u) : ∃ (_ : LinearOrder α), WellFoundedLT α`. It comes from `nonempty_embedding_to_cardinal : Nonempty (α ↪ Cardinal.{u})` and the pulled back relation `WellOrderingRel`, with the proof above.

<?decl exists_wellFoundedLT?>
:::

Common errors of a learner:

- `Order.succ c` is not `c + 1` for infinite `c`. For $c = \aleph_0$, $c + 1 = \aleph_0$, but $\mathrm{succ}\,\aleph_0 = \aleph_1$.
- `sSup s` and `⨆ i, f i` are junk when the set is not bounded above. Lemmas such as `le_ciSup` need a proof of `BddAbove (Set.range f)`. For `ι : Type u` and values in `Cardinal.{u}`, `Cardinal.bddAbove_of_small` provides it.
- Jech and Kunen require a strong limit to be uncountable. Mathlib does not, so `ℵ₀` is a strong limit. A statement about uncountable strong limits needs the extra hypothesis `ℵ₀ < c`.
- `2 ^ a` with `a : Cardinal` is cardinal power, but `2 ^ n` with `n : ℕ` is a natural number. Write `(2 : Cardinal) ^ (n : Cardinal)` when the cast matters.

### Exercises

1. (A) Show that $\mathrm{succ}\,0 = 1$ and $\mathrm{succ}\,1 = 2$ directly from the definition of the order.
2. (A) Show that $0$ is a strong prelimit but not a strong limit, and that $1$ and $2$ are not strong prelimits.
3. (A) Deduce Cantor's theorem from König's theorem, and identify each sum and product with a type.
4. (B) Show that $\prod_{n \ge 1} n = 2^{\aleph_0}$. Hint: compare with $\prod_n 2$ and $\prod_n \aleph_0$, and use $\aleph_0 \cdot \aleph_0 = \aleph_0$ from Section 3.
5. (B) Let $(c_i)_{i \in \iota}$ be a family with $\iota$ in universe $u$. Show that $\sup_i c_i \le \sum_i c_i \le \#\iota \cdot \sup_i c_i$. Hint: for the second, embed each $c_i.\mathrm{out}$ in a fixed type of cardinal $\sup_i c_i$.
6. (B) Show that $\aleph_0 = \#\mathbb{N}$ is a strong limit in the sense of Mathlib, and that $2^{\aleph_0}$ is not. Hint: for the first, $2^n$ is finite for finite $n$.
7. (C) Let $\kappa$ be an infinite cardinal and $(\kappa_n)$ a strictly increasing sequence with $\sup_n \kappa_n = \kappa$. Use König's theorem with $f_n = \kappa_n$ and $g_n = \kappa$ to show $\kappa < \kappa^{\aleph_0}$. Hint: $\sum_n \kappa_n = \kappa$.

### Notes and history

Cantor proved that a set has smaller cardinality than its power set in 1891, with the diagonal method. Julius König stated the inequality between sums and products in 1905. Zermelo proved the well-ordering theorem from the axiom of choice in 1904. Jech, *Set Theory*, Chapter 5, and Kunen, *Set Theory*, Chapter I, give König's theorem and its consequences for cofinality, which Chapter 5 of this volume treats.

### Reference

<?reference?>
