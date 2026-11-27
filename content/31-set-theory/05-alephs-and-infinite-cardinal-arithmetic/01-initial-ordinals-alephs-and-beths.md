---
title: Initial ordinals, alephs and beths
kind: theory
modules:
  - Mathlib.SetTheory.Cardinal.Ordinal
  - Mathlib.SetTheory.Cardinal.Aleph
explains:
  E3: [Ordinal.IsInitial, Cardinal.preAleph, Cardinal.aleph, Ordinal.omega, Cardinal.beth]
  E2: [Ordinal.isInitialIso, Ordinal.preOmega, Cardinal.preBeth, Cardinal.isNormal_aleph, Cardinal.range_aleph, Cardinal.succ_aleph, Cardinal.aleph_limit, Cardinal.ord_aleph, Ordinal.card_omega, Cardinal.aleph_one_le_iff, Cardinal.lt_aleph_one_iff, Cardinal.lt_omega_iff_card_lt, Cardinal.beth_add_one, Cardinal.aleph_le_beth, Cardinal.isStrongLimit_beth, Cardinal.mk_biUnion_le_of_le, Ordinal.card_opow_le, Ordinal.isPrincipal_add_ord]
  E1: auto
families: []
requires: [V04.C06, V31.C01, V31.C02, V31.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Initial ordinals, alephs and beths

### Overview

Many ordinals have the same cardinality: $\omega$, $\omega + 1$ and $\omega^\omega$ are all countable. The least ordinal of a given cardinality is the initial ordinal of that cardinality. The initial ordinals give each cardinal a canonical representative among the ordinals, and they let the ordinals count the cardinals. The infinite initial ordinals in increasing order are $\omega_0 = \omega, \omega_1, \omega_2, \ldots$, and their cardinalities are the alephs $\aleph_0 < \aleph_1 < \aleph_2 < \cdots$. The main theorem says that $\alpha \mapsto \aleph_\alpha$ is a normal function onto the infinite cardinals.

A second scale comes from the power set: the beths, with $\beth_0 = \aleph_0$ and $\beth_{\alpha+1} = 2^{\beth_\alpha}$. Cantor's theorem gives $\aleph_\alpha \le \beth_\alpha$. The section ends with bounds on ordinal-indexed unions and on ordinal powers. These bounds use the theorem $\kappa \cdot \kappa = \kappa$ of Section 2, whose proof does not use this section.

### Definitions

Chapter 2 defined $\operatorname{ord} c$, the least ordinal of cardinality $c$. Two facts are used here: $\operatorname{card}(\operatorname{ord} c) = c$, and $\operatorname{ord} c \le o$ if and only if $c \le \operatorname{card} o$. The second fact is a Galois connection (Volume 4, Chapter 6). Its contrapositive is $o < \operatorname{ord} c$ if and only if $\operatorname{card} o < c$.

::: mathlib
`Cardinal.gc_ord_card` · `Mathlib.SetTheory.Ordinal.Basic`

`GaloisConnection ord card`, with the halves `Cardinal.ord_le : ord c ≤ o ↔ c ≤ o.card` and `Cardinal.lt_ord : o < ord c ↔ o.card < c`, and `Cardinal.card_ord : (ord c).card = c`. These belong to Chapter 2.

<?decl Cardinal.gc_ord_card?>
:::

**Definition (Initial ordinal).** An ordinal $o$ is *initial* if $\operatorname{ord}(\operatorname{card} o) = o$.

The natural numbers and $\omega$ are initial. The ordinal $\omega + 1$ is not, since $\omega < \omega + 1$ and both are countable.

::: mathlib
`Ordinal.IsInitial` · `Mathlib.SetTheory.Cardinal.Aleph`

`IsInitial o` is defined as `o.card.ord = o`. The lemma `Ordinal.isInitial_ord` says that each `ord c` is initial, and `Ordinal.IsInitial.card_lt_card` says that for an initial `b`, `a.card < b.card ↔ a < b`. The map `Ordinal.isInitialIso : {x // IsInitial x} ≃o Cardinal` is the restriction of `card`.

<?decl Ordinal.IsInitial?>
:::

**Definition (Omegas and alephs).** Let $e$ be the order isomorphism from the ordinals onto the class of initial ordinals, which the enumeration theorem below provides. Put $\omega_\alpha = e(\omega + \alpha)$ and $\aleph_\alpha = \operatorname{card}(\omega_\alpha)$.

The shift by $\omega$ skips the finite initial ordinals, which are the values $e(n) = n$. So $\omega_0 = \omega$ and $\aleph_0 = |\mathbb{N}|$.

::: mathlib
`Ordinal.preOmega` · `Mathlib.SetTheory.Cardinal.Aleph`

`preOmega : Ordinal ↪o Ordinal` is the map $e$. It is `Order.enum` of the set `{x | IsInitial x}`, which is cofinal by `Ordinal.isCofinal_setOfPred_isInitial`; `Order.enum` belongs to the cofinality library of Chapter 6. Then `Ordinal.omega`, with notation `ω_ o`, is `preOmega (ω + o)`, and `ω₁` is `ω_ 1`.

<?decl Ordinal.preOmega?>
:::

<?decl Ordinal.omega?>

::: mathlib
`Cardinal.preAleph` · `Mathlib.SetTheory.Cardinal.Aleph`

`preAleph : Ordinal ≃o Cardinal` is the composite of `Order.enum` with `isInitialIso`. It is an isomorphism, with `preAleph n = n` (`Cardinal.preAleph_natCast`) and `preAleph ω = ℵ₀`. The aleph map `Cardinal.aleph : Ordinal ↪o Cardinal`, with notation `ℵ_ o`, is `preAleph (ω + o)`, and `ℵ₁` is `ℵ_ 1`. The lemmas `Cardinal.ord_aleph : (ℵ_ o).ord = ω_ o` and `Ordinal.card_omega : (ω_ o).card = ℵ_ o` link the two scales.

<?decl Cardinal.preAleph?>
:::

<?decl Cardinal.aleph?>

**Definition (Beth numbers).** Define $\beth_0 = \aleph_0$, $\beth_{\alpha+1} = 2^{\beth_\alpha}$, and $\beth_\lambda = \sup_{\alpha < \lambda} \beth_\alpha$ for a limit ordinal $\lambda$.

::: mathlib
`Cardinal.beth` · `Mathlib.SetTheory.Cardinal.Aleph`

Mathlib first defines `preBeth o = ⨆ a : Iio o, 2 ^ preBeth a`, one clause for all ordinals. The empty supremum gives `preBeth 0 = 0`; then come $1, 2, 4, 16, \ldots$, and `preBeth ω = ℵ₀`. Then `beth o = preBeth (ω + o)`, with notation `ℶ_ o`. The textbook clauses are the lemmas `Cardinal.beth_zero`, `Cardinal.beth_add_one : ℶ_ (o + 1) = 2 ^ ℶ_ o` and `Cardinal.beth_limit`.

<?decl Cardinal.beth?>
:::

<?decl Cardinal.preBeth?>

### Theorems and proofs

**Proposition (Initial ordinals).** An ordinal $o$ is initial if and only if $\operatorname{card} a < \operatorname{card} o$ for each $a < o$. Each $\operatorname{ord} c$ is initial, and $\operatorname{card}$ is an order isomorphism from the initial ordinals onto the cardinals, with inverse $\operatorname{ord}$.

*Proof.* Put $c = \operatorname{card} o$. The Galois connection gives $\operatorname{ord} c \le o$. If $o = \operatorname{ord} c$ and $a < o$, then $\operatorname{card} a < c$ by the contrapositive form. Conversely, if each $a < o$ has $\operatorname{card} a < c$, then $\operatorname{ord} c < o$ is impossible, since $\operatorname{ord} c$ has cardinality $c$. So $\operatorname{ord} c = o$. From $\operatorname{card}(\operatorname{ord} c) = c$ follows $\operatorname{ord}(\operatorname{card}(\operatorname{ord} c)) = \operatorname{ord} c$. So $\operatorname{ord}$ and $\operatorname{card}$ are inverse bijections between the cardinals and the initial ordinals. Both are monotone, so they are order isomorphisms. $\square$

**Theorem (Enumeration of the initial ordinals).** The initial ordinals are unbounded, and there is an order isomorphism $e$ from the ordinals onto the initial ordinals. So $\alpha \mapsto \operatorname{card}(e(\alpha))$ is an order isomorphism from the ordinals onto the cardinals.

*Proof.* Unbounded: given $o$, let $c$ be the successor cardinal of $\operatorname{card} o$. It exists since the cardinals are well ordered and $2^{\operatorname{card} o} > \operatorname{card} o$ (Chapter 1). If $\operatorname{ord} c \le o$, then $c \le \operatorname{card} o$, which is false. So the initial ordinal $\operatorname{ord} c$ is above $o$.

Existence: let $e(\alpha)$ be the least initial ordinal above all $e(\beta)$, $\beta < \alpha$. The values $e(\beta)$ form a set, so they have an upper bound, and an initial ordinal above it exists. So $e$ is defined and strictly increasing. Onto: let $x$ be initial and not a value of $e$. By induction, $e(\alpha) < x$ for each $\alpha$: if $e(\beta) < x$ for all $\beta < \alpha$, then $e(\alpha) \le x$ by minimality, and $e(\alpha) \ne x$. So $e$ injects all ordinals into the set of ordinals below $x$. This contradicts the Burali-Forti theorem of Chapter 2. The last claim composes $e$ with the proposition. $\square$

**Theorem (Alephs).** The map $\alpha \mapsto \aleph_\alpha$ is strictly increasing and its range is the class of infinite cardinals. The cardinal $\aleph_{\alpha+1}$ is the successor of $\aleph_\alpha$, and $\aleph_\lambda = \sup_{\alpha < \lambda} \aleph_\alpha$ for a limit $\lambda$. So the map is normal in the sense of Chapter 4.

*Proof.* Let $p$ be the isomorphism $\alpha \mapsto \operatorname{card}(e(\alpha))$, so $\aleph_\alpha = p(\omega + \alpha)$. The map is strictly increasing as a composite of two such maps, and each value is at least $p(\omega) = \aleph_0$. For $c \ge \aleph_0$, the ordinal $o = p^{-1}(c)$ satisfies $o \ge \omega$, so $o = \omega + (o - \omega)$ and $c = \aleph_{o - \omega}$. An order isomorphism preserves successors, and $\omega + (\alpha + 1) = (\omega + \alpha) + 1$, so $\aleph_{\alpha+1} = \operatorname{succ}\aleph_\alpha$. For a limit $\lambda$, let $s = \sup_{\alpha<\lambda} \aleph_\alpha \le \aleph_\lambda$. Then $s$ is infinite, so $s = \aleph_\gamma$. Each $\alpha < \lambda$ has $\alpha + 1 < \lambda$ and $\aleph_\alpha < \aleph_{\alpha+1} \le \aleph_\gamma$, so $\alpha < \gamma$. Thus $\lambda \le \gamma$ and $\aleph_\lambda \le s$. $\square$

**Corollary (The first uncountable cardinal).** $\aleph_1 \le c$ if and only if $\aleph_0 < c$. An ordinal $o$ satisfies $o < \omega_1$ if and only if $o$ is countable.

*Proof.* The first claim restates $\aleph_1 = \operatorname{succ}\aleph_0$. The ordinal $\omega_1$ is initial of cardinality $\aleph_1$, so $o < \omega_1$ if and only if $\operatorname{card} o < \aleph_1$, that is $\operatorname{card} o \le \aleph_0$. $\square$

**Theorem (Alephs and beths).** $\aleph_\alpha \le \beth_\alpha$ for each $\alpha$. The cardinal $\beth_\alpha$ is a strong limit if and only if $\alpha$ is $0$ or a limit ordinal.

*Proof.* Induction on $\alpha$. At $0$ both sides are $\aleph_0$. At a successor, $\aleph_{\alpha+1} = \operatorname{succ}\aleph_\alpha \le \operatorname{succ}\beth_\alpha \le 2^{\beth_\alpha}$ by Cantor's theorem. At a limit, take suprema.

A strong limit $c$ is nonzero with $2^x < c$ for all $x < c$ (Chapter 1). The beths are strictly increasing. If $\alpha = \beta + 1$, then $x = \beth_\beta < \beth_\alpha$ and $2^x = \beth_\alpha$. For $\alpha = 0$, each $x < \aleph_0$ is finite and so is $2^x$. For a limit $\lambda$ and $x < \beth_\lambda$, some $\beta < \lambda$ has $x < \beth_\beta$, and then $2^x \le \beth_{\beta+1} < \beth_{\beta+2} \le \beth_\lambda$. $\square$

**Theorem (Ordinal-indexed bounds).** Let $c$ be an infinite cardinal.

1. If $\operatorname{card} o \le c$ and $|A_j| \le c$ for each $j < o$, then $|\bigcup_{j<o} A_j| \le c$.
2. $\operatorname{card}(a^b) \le \max(\aleph_0, \operatorname{card} a, \operatorname{card} b)$ for all ordinals $a, b$.
3. If $a, b < \operatorname{ord} c$, then $a + b$, $a \cdot b$ and $a^b$ are smaller than $\operatorname{ord} c$.

*Proof.* Item 1: the union is the image of the disjoint union, so its cardinality is at most $\sum_{j<o} |A_j| \le \operatorname{card}(o) \cdot c \le c \cdot c = c$, by Section 2. The same argument bounds a supremum of ordinals: the ordinals below $\sup_i f_i$ are the union of the ordinals below each $f_i$.

Item 2: put $\kappa = \max(\aleph_0, \operatorname{card} a, \operatorname{card} b)$. If $a = 0$, then $a^b \le 1$. Otherwise prove $\operatorname{card}(a^x) \le \kappa$ for $x \le b$ by induction. At $0$, $a^0 = 1$. At a successor, $\operatorname{card}(a^x \cdot a) \le \kappa \cdot \kappa = \kappa$. At a limit $x$, $a^x = \sup_{y<x} a^y$ has at most $\operatorname{card} x \le \kappa$ terms, and item 1 applies.

Item 3: $\operatorname{card} a, \operatorname{card} b < c$, and Section 2 gives $\operatorname{card} a + \operatorname{card} b < c$ and $\operatorname{card} a \cdot \operatorname{card} b < c$. These are the cardinalities of $a + b$ and $a \cdot b$. For $a^b$: if $c = \aleph_0$, then $a^b$ is finite; if $c > \aleph_0$, use item 2. $\square$

In the language of Chapter 4, each infinite initial ordinal is additively, multiplicatively and exponentially principal.

### Examples

**Example (Computations).** The theorem on alephs gives $\aleph_{\omega+1} = \operatorname{succ}\aleph_\omega$ and $\aleph_\omega = \sup_n \aleph_n$. Item 2 gives $\operatorname{card}(\omega^\omega) = \aleph_0$, so $\omega^\omega < \omega_1$. The ordinal $\omega_1 + \omega$ has cardinality $\aleph_1 + \aleph_0 = \aleph_1$, so it lies between $\omega_1$ and $\omega_2$. The beths give $\beth_1 = 2^{\aleph_0}$, the cardinality of $\mathbb{R}$ (Section 3), and $\beth_2 = 2^{2^{\aleph_0}}$.

**Example ($\omega_1$ is an epsilon number).** The map $x \mapsto \omega^x$ is normal (Chapter 4). For $x < \omega_1$, item 3 with $c = \aleph_1$ gives $\omega^x < \omega_1$. As $\omega_1$ is a limit, $\omega^{\omega_1} = \sup_{x<\omega_1} \omega^x \le \omega_1 \le \omega^{\omega_1}$. So $\omega^{\omega_1} = \omega_1$, and the same holds for each $\omega_\alpha$ with $\alpha \ge 1$.

**Counterexample (The limit clause needs a limit).** For $\lambda = \beta + 1$, $\sup_{\alpha<\lambda} \aleph_\alpha = \aleph_\beta < \aleph_\lambda$. In the same way, $\beth_1$ is not a strong limit: $\aleph_0 < \beth_1$ and $2^{\aleph_0} = \beth_1$.

**Counterexample (Item 1 needs an infinite bound).** Take $c = 2$, $o = 2$, $A_0 = \{0, 1\}$ and $A_1 = \{2, 3\}$. The hypotheses hold except $c \ge \aleph_0$, and the union has 4 elements. The step $c \cdot c = c$ fails for $c = 2$.

### The library around it

::: mathlib
`Cardinal.isNormal_aleph` · `Mathlib.SetTheory.Cardinal.Aleph`

`isNormal_aleph : Order.IsNormal aleph`. From it come `Cardinal.aleph_limit (ho : IsSuccLimit o) : ℵ_ o = ⨆ a : Iio o, ℵ_ a` and `Cardinal.succ_aleph : succ (ℵ_ o) = ℵ_ (o + 1)`. The range is `Cardinal.range_aleph : range aleph = Set.Ici ℵ₀`. For $\aleph_1$ use `Cardinal.aleph_one_le_iff` and `Cardinal.lt_aleph_one_iff : c < ℵ₁ ↔ c ≤ ℵ₀`.

<?decl Cardinal.isNormal_aleph?>
:::

::: mathlib
`Cardinal.isStrongLimit_beth` · `Mathlib.SetTheory.Cardinal.Aleph`

`isStrongLimit_beth : IsStrongLimit (ℶ_ o) ↔ IsSuccPrelimit o`. A successor prelimit is an ordinal that is not a successor, so $0$ counts. The lemma `Cardinal.isStrongLimit_preBeth` for `preBeth` needs `IsSuccLimit o` instead, because `preBeth 0 = 0`. The bound is `Cardinal.aleph_le_beth : ℵ_ o ≤ ℶ_ o`.

<?decl Cardinal.isStrongLimit_beth?>
:::

::: mathlib
`Cardinal.mk_biUnion_le_of_le` · `Mathlib.SetTheory.Cardinal.Ordinal`

`mk_biUnion_le_of_le (ho : o.card ≤ c) (hc : ℵ₀ ≤ c) (A : Ordinal → Set β) (hA : ∀ j < o, #(A j) ≤ c) : #(⋃ j < o, A j) ≤ c` is item 1. Item 2 is `Ordinal.card_opow_le`, and item 3 is `Ordinal.isPrincipal_add_ord`, `Ordinal.isPrincipal_mul_ord` and `Ordinal.isPrincipal_opow_ord`, stated with the predicate `IsPrincipal` of Chapter 4.

<?decl Cardinal.mk_biUnion_le_of_le?>
:::

<?decl Ordinal.card_opow_le?>

<?decl Ordinal.isPrincipal_add_ord?>

Common errors of a learner:

- The index of `ℵ_` is an ordinal. `ℵ₀` is a separate constant, equal to `ℵ_ 0` by `Cardinal.aleph_zero`.
- `ω_ o` is an ordinal and `ℵ_ o` is a cardinal. The ordinal `ω` is `ω_ 0`, not `ω_ 1`.
- `preAleph` and `aleph` differ by the shift $\omega + o$. A lemma found by search may be stated for the wrong one.
- A supremum of cardinals is the true supremum only for a family bounded above (Volume 4, Chapter 5). A family indexed by a small type is bounded, by `Cardinal.bddAbove_of_small`.
- To show that an ordinal is below $\omega_\alpha$, use `Cardinal.lt_omega_iff_card_lt : x < ω_ o ↔ x.card < ℵ_ o` and compare cardinalities.

### Exercises

1. (A) Show that $\omega \cdot 2$ and $\omega^2$ are not initial, and that each natural number is initial.
2. (A) Compute $\aleph_3 + \aleph_\omega$, $\operatorname{card}(\omega_2 \cdot \omega_1)$ and $\operatorname{card}(\omega_1^{\omega})$. Hint: use Section 2 and item 2.
3. (A) Show that $\beth_\omega$ is a strong limit and that $\beth_\omega < \beth_{\omega+1}$.
4. (B) Show that each infinite initial ordinal is a limit ordinal. Hint: if $a$ is infinite, then $\operatorname{card}(a + 1) = \operatorname{card} a$.
5. (B) Show that the supremum of a nonempty set of initial ordinals is initial.
6. (B) Show that the generalized continuum hypothesis, $2^{\aleph_\alpha} = \aleph_{\alpha+1}$ for all $\alpha$, is equivalent to $\aleph_\alpha = \beth_\alpha$ for all $\alpha$.
7. (C) Put $\theta_0 = 0$, $\theta_{n+1} = \omega_{\theta_n}$ and $\theta = \sup_n \theta_n$. Show that $\omega_\theta = \theta$ and that $\theta$ is the least fixed point of $\alpha \mapsto \omega_\alpha$. Hint: normality, and $\theta_n \le \varphi$ for each fixed point $\varphi$.

### Notes and history

Cantor introduced the alephs in his *Beiträge zur Begründung der transfiniten Mengenlehre* of 1895 and 1897. Hartogs showed in 1915, without the axiom of choice, that for each set there is a least ordinal that does not inject into it. Gödel proved in 1938 that the generalized continuum hypothesis is consistent with the axioms of set theory, and Cohen proved in 1963 that its negation is consistent too. The index of this edition has no declaration for either result.

### Reference

<?reference?>
