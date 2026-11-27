---
title: The arithmetic of infinite cardinals
kind: theory
modules:
  - Mathlib.SetTheory.Cardinal.Arithmetic
  - Mathlib.SetTheory.Cardinal.Divisibility
  - Mathlib.SetTheory.Cardinal.EventuallyConst
  - Mathlib.SetTheory.Cardinal.CountableCover
  - Mathlib.SetTheory.Cardinal.DirectLimit
  - Mathlib.SetTheory.Cardinal.HasCardinalLT
explains:
  E3: [Cardinal.mul_eq_self, Cardinal.add_eq_self, Cardinal.power_self_eq, Cardinal.prime_of_aleph0_le, HasCardinalLT]
  E2: [Cardinal.mul_eq_max, Cardinal.add_eq_max, Cardinal.mul_lt_of_lt, Cardinal.add_lt_of_lt, Cardinal.mul_eq_max_of_aleph0_le_left, Cardinal.aleph_mul_aleph, Cardinal.power_nat_eq, Cardinal.power_eq_two_power, Cardinal.mk_list_eq_max, Cardinal.mk_finset_of_infinite, Cardinal.mk_perm_eq_two_power, Cardinal.not_irreducible_of_aleph0_le, Cardinal.prime_iff, Cardinal.mk_le_of_countable_eventually_mem, DirectLimit.mk_le_of_aleph0_le, HasCardinalLT.of_injective, Cardinal.eventuallyConst_of_monotone, Filter.EventuallyConst.of_monotone_of_lt_cof]
  E1: auto
families: []
requires: [V31.C01, V31.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The arithmetic of infinite cardinals

### Overview

For finite cardinals, $n + n = 2n$ and $n \cdot n = n^2$, and both are larger than $n$ when $n \ge 2$. For infinite cardinals the picture collapses: $\kappa + \kappa = \kappa \cdot \kappa = \kappa$. This is Hessenberg's theorem, and it is the main result of this section. From it, the sum and the product of two cardinals, one of them infinite and both nonzero, are their maximum. Exponentiation does not collapse in the same way, but $\kappa^\kappa = 2^\kappa$ and $\kappa^n = \kappa$ for $1 \le n < \aleph_0$.

The section then counts lists, finite sets and permutations, shows that each infinite cardinal is prime, and presents small tools of Mathlib that rest on the theorem. The proofs use the well-orders of Chapter 2, but nothing from Section 1.

### Definitions

**Definition (The order of Gödel on pairs).** Let $(A, <)$ be a linear order. On $A \times A$, put $(x, y) \prec (x', y')$ if the triple $(\max(x, y), x, y)$ is smaller than $(\max(x', y'), x', y')$ in the lexicographic order of $A \times A \times A$.

The map $(x, y) \mapsto (\max(x, y), x, y)$ is injective, and the lexicographic order of well-orders is a well-order. So $\prec$ is a well-order when $<$ is one. The pairs below $(a, b)$ all have both coordinates at most $\max(a, b)$. This is the property that the lexicographic order of $A \times A$ lacks: below $(1, 0)$ in that order lie all the pairs $(0, y)$.

**Definition (Divisibility of cardinals).** For cardinals $a$ and $b$, $a \mid b$ means $b = a \cdot c$ for some cardinal $c$. A cardinal $p$ is *prime* if $p \ne 0$, $p$ is not a unit, and $p \mid a \cdot b$ implies $p \mid a$ or $p \mid b$.

These are the definitions of Volume 6 for a commutative monoid with zero. The cardinals form a commutative semiring, so they apply.

**Definition (Cardinality below a bound).** For a type $X$ and a cardinal $\kappa$, possibly in another universe, `HasCardinalLT X κ` means $|X| < \kappa$, with both sides lifted to a common universe.

### Theorems and proofs

**Theorem (Hessenberg).** For each infinite cardinal $\kappa$, $\kappa \cdot \kappa = \kappa$.

*Proof.* Since $1 \le \kappa$, $\kappa = \kappa \cdot 1 \le \kappa \cdot \kappa$. The other inequality is proved by well-founded induction on $\kappa$. Assume $\mu \cdot \mu = \mu$ for each infinite $\mu < \kappa$. Then $\mu \cdot \mu < \kappa$ for every $\mu < \kappa$: a finite $\mu$ has finite square, and an infinite $\mu$ has square $\mu$.

Let $A$ be a set of cardinality $\kappa$ with a well-order of type $\operatorname{ord} \kappa$ (Chapter 2). For $q \in A$, the initial segment $A_{<q}$ has an order type smaller than $\operatorname{ord} \kappa$, so $|A_{<q}| < \kappa$. The order has no largest element: $\operatorname{ord} \kappa$ is a limit ordinal, since $\operatorname{card}(o + 1) = \operatorname{card} o$ for infinite $o$.

Order $A \times A$ by the order $\prec$ of Gödel. Fix a pair $(a, b)$ and choose $q \in A$ with $q > \max(a, b)$. If $(x, y) \prec (a, b)$, then $\max(x, y) \le \max(a, b) < q$, so $(x, y) \in A_{<q} \times A_{<q}$. So the pairs below $(a, b)$ number at most $|A_{<q}|^2 < \kappa$.

It remains to see that a well-ordered set $W$ in which each element has fewer than $\kappa$ predecessors has $|W| \le \kappa$. Let $t$ be its order type. Each $w \in W$ has a predecessor set of order type $o_w$ with $\operatorname{card} o_w < \kappa$, so $o_w < \operatorname{ord} \kappa$. The order types $o_w$ are exactly the ordinals below $t$, so $t \le \operatorname{ord} \kappa$ and $|W| = \operatorname{card} t \le \kappa$. With $W = (A \times A, \prec)$, this gives $\kappa \cdot \kappa \le \kappa$. $\square$

The proof in Mathlib follows the same route. It embeds $A \times A$ into the lexicographic product by $(x, y) \mapsto (\max(x, y), x, y)$, and the last step is the lemma `Ordinal.mk_le_of_forall_mk_setOfPred_lt`.

**Corollary (Sums and products).** Let $a$ be infinite.

1. $a + b = \max(a, b)$ for each $b$, and $a \cdot b = \max(a, b)$ for each $b \ne 0$.
2. If $c$ is infinite and $a', b' < c$, then $a' + b' < c$ and $a' \cdot b' < c$.
3. $\aleph_\alpha \cdot \aleph_\beta = \aleph_\alpha + \aleph_\beta = \aleph_{\max(\alpha, \beta)}$.

*Proof.* Put $m = \max(a, b)$, which is infinite. For item 1, $a \le a + b$ and $b \le a + b$, so $m \le a + b \le m + m = m \cdot 2 \le m \cdot m = m$. If $b \ne 0$, then $1 \le b$ and $1 \le a$, so $a \le a \cdot b$ and $b \le a \cdot b$. Thus $m \le a \cdot b \le m \cdot m = m$. For item 2, put $m' = \max(a', b') < c$. If $m'$ is finite, the sum and the product are finite, hence smaller than $c$. Otherwise both are at most $m' \cdot m' = m' < c$. Item 3 is item 1 with the monotonicity of the alephs. $\square$

**Corollary (Powers).** Let $\kappa$ be infinite. Then $\kappa^n = \kappa$ for each natural number $n \ge 1$, $\kappa^\kappa = 2^\kappa$, and $\mu^\kappa = 2^\kappa$ for each $\mu$ with $2 \le \mu \le \kappa$.

*Proof.* The first claim is induction on $n$, with $\kappa^{n+1} = \kappa^n \cdot \kappa = \kappa \cdot \kappa = \kappa$. For the second, $2 \le \kappa < 2^\kappa$, so $2^\kappa \le \kappa^\kappa \le (2^\kappa)^\kappa = 2^{\kappa \cdot \kappa} = 2^\kappa$. The third lies between $2^\kappa$ and $\kappa^\kappa$. $\square$

**Proposition (Lists, finite sets and permutations).** For a nonempty type $\alpha$, $|\mathrm{List}\,\alpha| = \max(\aleph_0, |\alpha|)$. For an infinite $\alpha$, $|\mathrm{Finset}\,\alpha| = |\alpha|$ and $|\mathrm{Perm}\,\alpha| = 2^{|\alpha|}$.

*Proof.* A list is a pair of a length $n$ and a function from $\{0, \ldots, n-1\}$ to $\alpha$, so $|\mathrm{List}\,\alpha| = \sum_{n} |\alpha|^n$. If $\alpha$ is finite and nonempty, this is a countable sum of finite nonzero terms, so it is $\aleph_0$. If $\alpha$ is infinite with $|\alpha| = \kappa$, the sum is $1 + \sum_{n \ge 1} \kappa = 1 + \aleph_0 \cdot \kappa = \kappa$.

For finite sets, the map from lists to finite sets that forgets order and repetition is onto, so $|\mathrm{Finset}\,\alpha| \le \kappa$. The singletons give $\kappa \le |\mathrm{Finset}\,\alpha|$. For permutations, $|\mathrm{Perm}\,\alpha| \le \kappa^\kappa = 2^\kappa$. For the lower bound, write $\alpha$ as $\beta \times \{0, 1\}$, which is possible since $\kappa \cdot 2 = \kappa$. Each subset $S$ of $\beta$ gives the permutation that swaps $(x, 0)$ and $(x, 1)$ for $x \in S$. Distinct subsets give distinct permutations, and $|\beta| = \kappa$, so $2^\kappa \le |\mathrm{Perm}\,\alpha|$. $\square$

**Theorem (Infinite cardinals are prime).** Each infinite cardinal $\kappa$ is prime and is not irreducible. The only unit of the cardinals is $1$. A finite cardinal $n$ is prime if and only if $n$ is a prime number.

*Proof.* Units: if $a \cdot b = 1$, then $a, b \ne 0$, so $a \le a \cdot b = 1$ and $a = 1$.

Divisors of $\kappa$: $\kappa \mid x$ holds if and only if $x = 0$ or $\kappa \le x$. Indeed, if $x = \kappa \cdot y$, then $y = 0$ gives $x = 0$, and $y \ne 0$ gives $x \ge \kappa$. Conversely $0 = \kappa \cdot 0$, and if $\kappa \le x$, then $x$ is infinite and $x = \kappa \cdot x$ by the corollary.

Prime: $\kappa \ne 0$ and $\kappa \ne 1$. Let $\kappa \mid a \cdot b$. If $a \cdot b = 0$, then $a = 0$ or $b = 0$, and $\kappa$ divides $0$. Otherwise $a \cdot b \ge \kappa$ is infinite, so one factor is infinite and $a \cdot b = \max(a, b)$. Then $\kappa \le a$ or $\kappa \le b$. Not irreducible: $\kappa = \kappa \cdot \aleph_0$, and neither factor is a unit. For a finite $n \ne 0$, an equation $n = a \cdot c$ forces $a$ and $c$ to be natural numbers, so the divisors of $n$ are those of $\mathbb{N}$. If $n$ is a prime number and $n \mid a \cdot b$ with $a \cdot b$ infinite, then the infinite factor is at least $n$, so $n$ divides it. If $a \cdot b$ is finite, the claim reduces to $\mathbb{N}$. $\square$

**Proposition (Countable covers).** Let $(f_i)_{i \in I}$ be a countable family of subsets of $\alpha$, each of cardinality at most $a$, and let $l$ be a filter on $I$ that is not $\bot$. If each $x \in t$ lies in $f_i$ for $l$-eventually all $i$, then $|t| \le a$.

*Proof.* If $a$ is infinite, then $t \subseteq \bigcup_i f_i$, since an eventual property holds somewhere. So $|t| \le \sum_i |f_i| \le \aleph_0 \cdot a = a$. If $a$ is finite, take a finite subset $s \subseteq t$. A finite intersection of eventual events is eventual, so some $f_i$ contains all of $s$, and $|s| \le a$. A set whose finite subsets all have at most $a$ elements has at most $a$ elements. $\square$

**Proposition (Monotone maps on the cardinals).** Let $\beta$ be a partial order whose cardinality is that of a set of the universe of the cardinals. Each monotone $f$ from the cardinals to $\beta$ is eventually constant.

*Proof.* Suppose not. Then for each cardinal $c$ there is $d > c$ with $f(d) \ne f(c)$, hence $f(c) < f(d)$. Choose by transfinite recursion cardinals $c_\alpha$ for all ordinals $\alpha$, with $c_\alpha$ above all earlier $c_\beta$ and $f(c_\alpha)$ above all earlier values. At each step, let $s$ be the supremum of the earlier $c_\beta$, a set-indexed family, and pick $d > s$ with $f(d) > f(s)$. Then $\alpha \mapsto f(c_\alpha)$ is strictly increasing, so it injects all ordinals into $\beta$. This contradicts the Burali-Forti theorem of Chapter 2. $\square$

The general form in Mathlib replaces the cardinals by a linear order $\alpha$ and asks $|\beta| < \operatorname{cf}(\alpha)$, with the cofinality of Chapter 6.

### Examples

**Example (Computations).** $\aleph_\omega \cdot \aleph_3 + \aleph_1^5 = \aleph_\omega + \aleph_1 = \aleph_\omega$. The set of finite subsets of $\mathbb{R}$ has the cardinality of $\mathbb{R}$. The permutations of $\mathbb{N}$ number $2^{\aleph_0}$. The functions $\mathbb{N} \to \mathbb{N}$ number $\aleph_0^{\aleph_0} = 2^{\aleph_0}$, by the corollary on powers with $\mu = \kappa = \aleph_0$.

**Counterexample (Finite cardinals).** Each result needs an infinite cardinal. $2 \cdot 2 = 4$, $1 + 1 = 2$ and $3^3 = 27 \ne 2^3$. The finite cardinal $6$ is not prime: $6 \mid 2 \cdot 3$, but $6 \nmid 2$ and $6 \nmid 3$. The hypothesis $b \ne 0$ in $a \cdot b = \max(a, b)$ is needed too: $\aleph_0 \cdot 0 = 0$.

### The library around it

::: mathlib
`Cardinal.mul_eq_self` · `Mathlib.SetTheory.Cardinal.Arithmetic`

`mul_eq_self (hc : ℵ₀ ≤ c) : c * c = c`, proved by `WellFoundedLT.induction` as above. `Cardinal.add_eq_self` is the form for sums. The working forms are `Cardinal.mul_eq_max (ha : ℵ₀ ≤ a) (hb : ℵ₀ ≤ b)`, `Cardinal.mul_eq_max_of_aleph0_le_left (h : ℵ₀ ≤ a) (h' : b ≠ 0)`, `Cardinal.add_eq_max (ha : ℵ₀ ≤ a)`, `Cardinal.mul_lt_of_lt` and `Cardinal.add_lt_of_lt`. For alephs, `Cardinal.aleph_mul_aleph : ℵ_ o₁ * ℵ_ o₂ = ℵ_ (max o₁ o₂)`.

<?decl Cardinal.mul_eq_self?>
:::

<?decl Cardinal.add_eq_self?>

::: mathlib
`Cardinal.power_self_eq` · `Mathlib.SetTheory.Cardinal.Arithmetic`

`power_self_eq (h : ℵ₀ ≤ c) : c ^ c = 2 ^ c`. Related: `Cardinal.power_eq_two_power (h₁ : ℵ₀ ≤ c₁) (h₂ : 2 ≤ c₂) (h₂' : c₂ ≤ c₁) : c₂ ^ c₁ = 2 ^ c₁` and `Cardinal.power_nat_eq (h1 : ℵ₀ ≤ c) (h2 : 1 ≤ n) : c ^ n = c`. The counting lemmas are `Cardinal.mk_list_eq_max`, `Cardinal.mk_finset_of_infinite` and `Cardinal.mk_perm_eq_two_power`.

<?decl Cardinal.power_self_eq?>
:::

::: mathlib
`Cardinal.prime_of_aleph0_le` · `Mathlib.SetTheory.Cardinal.Divisibility`

`prime_of_aleph0_le (ha : ℵ₀ ≤ a) : Prime a`, with `Prime` from the algebra library. Also `Cardinal.not_irreducible_of_aleph0_le` and `Cardinal.prime_iff : Prime a ↔ ℵ₀ ≤ a ∨ ∃ p : ℕ, a = p ∧ p.Prime`. The file has an instance `Unique Cardinalˣ`.

<?decl Cardinal.prime_of_aleph0_le?>
:::

::: mathlib
`HasCardinalLT` · `Mathlib.SetTheory.Cardinal.HasCardinalLT`

`HasCardinalLT X κ` is `lift #X < lift κ`, for `X : Type u` and `κ : Cardinal.{v}`. The two universes serve category theory, which bounds types of one universe by cardinals of another. The API has `HasCardinalLT.of_injective`, `HasCardinalLT.of_surjective`, `hasCardinalLT_sigma` for a regular `κ` (Chapter 6), and `HasCardinalLT.exists_regular_cardinal`.

<?decl HasCardinalLT?>
:::

<?decl HasCardinalLT.of_injective?>

::: mathlib
`Cardinal.mk_le_of_countable_eventually_mem` · `Mathlib.SetTheory.Cardinal.CountableCover`

`mk_le_of_countable_eventually_mem [Countable ι] {l : Filter ι} [NeBot l] (ht : ∀ x, ∀ᶠ i in l, x ∈ f i) (h'f : ∀ i, #(f i) ≤ a) : #α ≤ a`. The filter form covers an increasing sequence of sets and an ordinary cover. A direct limit is a quotient of a disjoint union, so `DirectLimit.mk_le_of_aleph0_le` bounds it by an infinite $c$ that bounds the index type and each component. Also `Cardinal.eventuallyConst_of_monotone` and `Filter.EventuallyConst.of_monotone_of_lt_cof` give eventual constancy.

<?decl Cardinal.mk_le_of_countable_eventually_mem?>
:::

<?decl DirectLimit.mk_le_of_aleph0_le?>

<?decl Cardinal.eventuallyConst_of_monotone?>

Common errors of a learner:

- `mul_eq_max` needs both factors infinite. With one infinite factor, use `mul_eq_max_of_aleph0_le_left` and supply $b \ne 0$.
- `Cardinal.add_one_eq` gives `a + 1 = a` for infinite `a`. The successor of a cardinal is `Order.succ a`, not `a + 1`.
- Divisibility of cardinals is not the divisibility of the natural numbers: $\aleph_0 \mid 0$ and $\aleph_0 \mid \aleph_1$, and $\aleph_0$ has many divisors.

### Exercises

1. (A) Compute $\aleph_2 \cdot \aleph_5 + \aleph_3$ and $(\aleph_1 + \aleph_0)^3$.
2. (A) Show that the set of finite sequences of real numbers has the cardinality of $\mathbb{R}$.
3. (B) Show that the lexicographic order on $\omega \times \omega$ has order type $\omega^2$ and that each element has finitely many predecessors in the order of Gödel. Deduce that the order of Gödel on $\omega \times \omega$ has type $\omega$.
4. (B) Show that $\kappa \mid \mu$ for infinite cardinals $\kappa \le \mu$, and find all divisors of $\aleph_0$.
5. (B) Let $V$ be a vector space over a field $K$ with an infinite basis $B$. Show that $|V| = \max(|K|, |B|)$. Hint: elements of $V$ are finite linear combinations.
6. (B) Show that the set of countable subsets of $\mathbb{R}$ has cardinality $2^{\aleph_0}$. Hint: $(2^{\aleph_0})^{\aleph_0}$.
7. (C) Prove Hessenberg's theorem by Zorn's lemma: take a maximal pair $(B, g)$ with $B \subseteq A$ infinite and $g : B \times B \to B$ a bijection, and show $|B| = |A|$.

### Notes and history

Hessenberg proved $\kappa \cdot \kappa = \kappa$ for the alephs in his *Grundbegriffe der Mengenlehre* of 1906. The order on pairs by the maximum is often attached to Gödel, who used it to well-order $\omega_\alpha \times \omega_\alpha$ in his work on the constructible sets. Tarski showed in 1924 that the statement $\kappa \cdot \kappa = \kappa$ for all infinite $\kappa$ implies the axiom of choice.

### Reference

<?reference?>
