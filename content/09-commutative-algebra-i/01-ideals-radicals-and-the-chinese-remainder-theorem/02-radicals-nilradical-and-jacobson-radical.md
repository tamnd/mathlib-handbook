---
title: Radicals, nilradical and Jacobson radical
kind: theory
modules:
  - Mathlib.RingTheory.Nilpotent.Lemmas
  - Mathlib.RingTheory.Ideal.MinimalPrime.Basic
explains:
  E3: [Ideal.radical, nilradical, Ideal.jacobson]
  E2: [Ideal.IsRadical, Ideal.mem_radical_iff, Ideal.radical_eq_sInf, nilradical_eq_sInf, mem_nilradical, Ideal.exists_le_prime_disjoint, Ideal.radical_idem, Ideal.IsPrime.isRadical, Ideal.radical_mul, Ideal.radical_inf, Ideal.radical_pow, Ideal.le_radical, Ideal.mem_jacobson_iff, Ring.mem_jacobson_iff, Ring.jacobson, Ideal.jacobson_bot, Ideal.radical_le_jacobson, Ideal.exists_minimalPrimes_le, Ideal.minimalPrimes, Ideal.sInf_minimalPrimes, nilradical_eq_bot_iff, Ideal.sInf_isPrime_of_isChain]
  E1: auto
families: []
requires: [V06.C02, V06.C03, V04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Radicals, nilradical and Jacobson radical

### Overview

The radical $\sqrt{I}$ collects the elements $x$ with $x^n \in I$. Its main property says that $\sqrt{I}$ is the intersection of the prime ideals that contain $I$. The proof uses Zorn's lemma to find a prime ideal that avoids a multiplicative set, a tool that Chapter 2 uses again. The section then proves that minimal primes exist, and it studies the Jacobson radical. Rings are commutative with $1$.

### Definitions

**Definition (Radical).** The radical of an ideal $I$ of $R$ is
$$\sqrt{I} = \{ x \in R : x^n \in I \text{ for some } n \ge 1 \}.$$
The ideal $I$ is radical if $\sqrt{I} = I$.

**Definition (Nilradical).** The nilradical of $R$ is $\mathfrak{N}(R) = \sqrt{0}$, the set of the nilpotent elements. The ring $R$ is reduced if $\mathfrak{N}(R) = 0$.

**Definition (Multiplicative set).** A subset $S \subseteq R$ is multiplicative if $1 \in S$ and $s t \in S$ for all $s, t \in S$. For $x \in R$ the powers $\{1, x, x^2, \dots\}$ form a multiplicative set, and so does $R \setminus P$ for a prime ideal $P$.

**Definition (Minimal prime).** A prime ideal $P$ is a minimal prime over $I$ if $I \subseteq P$ and no prime ideal $Q$ satisfies $I \subseteq Q \subsetneq P$. A minimal prime of $R$ is a minimal prime over $0$.

**Definition (Jacobson radical).** The Jacobson radical $J(I)$ of an ideal $I$ is the intersection of the maximal ideals that contain $I$. The Jacobson radical of $R$ is $J(R) = J(0)$, the intersection of all maximal ideals.

::: mathlib
`Ideal.radical` · `Mathlib.RingTheory.Ideal.Operations`

`I.radical` is the ideal of the `r` with `∃ n, r ^ n ∈ I` (`Ideal.mem_radical_iff`). `Ideal.IsRadical I` says `I.radical ≤ I`. `nilradical R` is `(0 : Ideal R).radical`, with `mem_nilradical : x ∈ nilradical R ↔ IsNilpotent x`. `nilradical_eq_bot_iff` says `nilradical R = ⊥ ↔ IsReduced R`.

<?decl Ideal.radical?>
:::

### Theorems and proofs

**Theorem (The radical is an ideal).** For each ideal $I$, $\sqrt{I}$ is an ideal that contains $I$.

*Proof.* Clearly $0 \in I \subseteq \sqrt{I}$. If $x^m \in I$, then $(r x)^m = r^m x^m \in I$ for each $r$. Let $a^m \in I$ and $b^n \in I$. By the binomial theorem
$$(a + b)^{m + n - 1} = \sum_{k = 0}^{m + n - 1} \binom{m + n - 1}{k} a^k b^{m + n - 1 - k}.$$
In each term $k \ge m$ or $m + n - 1 - k \ge n$, so each term lies in $I$. Hence $a + b \in \sqrt{I}$, and $-b \in \sqrt{I}$ since $(-b)^n = \pm b^n$. $\square$

**Theorem (Rules for radicals).** Let $I, J$ be ideals of $R$.

1. $\sqrt{\sqrt{I}} = \sqrt{I}$, and $I \subseteq J$ implies $\sqrt{I} \subseteq \sqrt{J}$.
2. $\sqrt{I J} = \sqrt{I \cap J} = \sqrt{I} \cap \sqrt{J}$, and $\sqrt{I^n} = \sqrt{I}$ for $n \ge 1$.
3. $\sqrt{I} = R$ if and only if $I = R$.
4. Each prime ideal is radical.

*Proof.* (1) If $(x^m)^n \in I$, then $x^{m n} \in I$. Monotony is clear.

(2) From $I J \subseteq I \cap J \subseteq I, J$ and (1) follow $\sqrt{I J} \subseteq \sqrt{I \cap J} \subseteq \sqrt{I} \cap \sqrt{J}$. If $x^m \in I$ and $x^n \in J$, then $x^{m + n} = x^m x^n \in I J$, so $\sqrt{I} \cap \sqrt{J} \subseteq \sqrt{I J}$. The case $I^n$ follows by induction from $\sqrt{I^{n} I} = \sqrt{I^n} \cap \sqrt{I}$.

(3) If $1 \in \sqrt{I}$, then $1 = 1^n \in I$.

(4) If $x^n \in P$ with $P$ prime, then $x \in P$ by induction on $n$. $\square$

::: mathlib
`Ideal.radical_mul` · `Mathlib.RingTheory.Ideal.Operations`

The rules are `Ideal.le_radical`, `Ideal.radical_idem`, `Ideal.radical_mul : (I * J).radical = I.radical ⊓ J.radical`, `Ideal.radical_inf`, `Ideal.radical_pow` (with the hypothesis `n ≠ 0`) and `Ideal.IsPrime.isRadical`.

<?decl Ideal.radical_mul?>
:::

**Theorem (Primes avoiding a multiplicative set).** Let $S$ be a multiplicative subset of $R$ and $I$ an ideal with $I \cap S = \emptyset$. Then there is a prime ideal $P \supseteq I$ with $P \cap S = \emptyset$.

*Proof.* Let $\Sigma$ be the set of ideals $J \supseteq I$ with $J \cap S = \emptyset$, ordered by inclusion. It contains $I$. The union of a nonempty chain in $\Sigma$ is an ideal, since two elements of the union lie in one member of the chain, and it contains $I$ and misses $S$. By Zorn's lemma (Volume 4) $\Sigma$ has a maximal element $P$. Since $1 \in S$, $P \ne R$.

Let $a, b \notin P$. The ideals $P + (a)$ and $P + (b)$ are strictly larger than $P$ and contain $I$, so by maximality they meet $S$: there are $s_1 = p_1 + r a$ and $s_2 = p_2 + t b$ in $S$ with $p_1, p_2 \in P$. Then
$$s_1 s_2 = (p_1 p_2 + p_1 t b + r a p_2) + r t \, a b.$$
The bracket lies in $P$. If $a b \in P$, then $s_1 s_2 \in P \cap S$, a contradiction. So $a b \notin P$, and $P$ is prime. $\square$

**Theorem (Radical as an intersection of primes).** For each ideal $I$ of $R$,
$$\sqrt{I} = \bigcap_{P \text{ prime}, \ P \supseteq I} P.$$
In particular $\mathfrak{N}(R)$ is the intersection of all prime ideals of $R$.

*Proof.* If $x^n \in I \subseteq P$ with $P$ prime, then $x \in P$. Conversely let $x \notin \sqrt{I}$. Then the multiplicative set $S = \{1, x, x^2, \dots\}$ misses $I$. By the previous theorem there is a prime $P \supseteq I$ with $x \notin P$. So $x$ is not in the intersection. $\square$

::: mathlib
`Ideal.exists_le_prime_disjoint` · `Mathlib.RingTheory.Ideal.Maximal`

The theorem on primes that avoid $S$, for a `Submonoid` `S`. Then `Ideal.radical_eq_sInf : I.radical = sInf {J | I ≤ J ∧ J.IsPrime}` and `nilradical_eq_sInf` state the intersection formula.

<?decl Ideal.exists_le_prime_disjoint?>
:::

**Theorem (Minimal primes exist).** Let $I \subseteq P$ with $P$ prime. Then $P$ contains a minimal prime over $I$. Consequently $\sqrt{I}$ is the intersection of the minimal primes over $I$.

*Proof.* Let $\Sigma$ be the set of primes $Q$ with $I \subseteq Q \subseteq P$, ordered by reverse inclusion. It contains $P$. Let $C$ be a nonempty chain in $\Sigma$ and $Q_0 = \bigcap_{Q \in C} Q$. Then $I \subseteq Q_0$ and $1 \notin Q_0$. Let $a b \in Q_0$ with $a \notin Q_0$, so $a \notin Q_1$ for some $Q_1 \in C$. Let $Q \in C$. If $Q \subseteq Q_1$, then $a \notin Q$ and $a b \in Q$, so $b \in Q$. If $Q_1 \subseteq Q$, then $b \in Q_1 \subseteq Q$, since $a b \in Q_1$ and $a \notin Q_1$. So $b \in Q_0$, and $Q_0$ is prime. By Zorn's lemma $\Sigma$ has an element minimal for inclusion. It is a minimal prime over $I$, since a smaller prime over $I$ would also lie in $\Sigma$.

Every prime over $I$ contains a minimal one, so the intersection of the minimal primes over $I$ equals the intersection of all primes over $I$, which is $\sqrt{I}$. $\square$

::: mathlib
`Ideal.exists_minimalPrimes_le` · `Mathlib.RingTheory.Ideal.MinimalPrime.Basic`

`Ideal.minimalPrimes I` is the set of minimal elements of `{p | p.IsPrime ∧ I ≤ p}`. The theorem is `Ideal.exists_minimalPrimes_le`, the corollary is `Ideal.sInf_minimalPrimes : sInf I.minimalPrimes = I.radical`, and the step on chains is `Ideal.sInf_isPrime_of_isChain`.

<?decl Ideal.exists_minimalPrimes_le?>
:::

**Theorem (Jacobson radical).** An element $x \in R$ lies in $J(R)$ if and only if $1 - x y$ is a unit for each $y \in R$. Also $\mathfrak{N}(R) \subseteq J(R)$.

*Proof.* Let $x \in J(R)$ and $y \in R$. If $1 - x y$ is not a unit, then the ideal $(1 - x y)$ is proper, so it lies in a maximal ideal $\mathfrak{m}$ by Volume 6, Chapter 2. Since $x \in \mathfrak{m}$, also $x y \in \mathfrak{m}$, and $1 = (1 - x y) + x y \in \mathfrak{m}$, a contradiction.

Conversely let $x \notin \mathfrak{m}$ for a maximal ideal $\mathfrak{m}$. Then $\mathfrak{m} + (x) = R$, so $1 = u + x y$ with $u \in \mathfrak{m}$. Then $1 - x y = u$ lies in a proper ideal and is not a unit.

Each maximal ideal is prime, so the intersection of all primes lies in the intersection of the maximal ideals. $\square$

::: mathlib
`Ideal.jacobson` · `Mathlib.RingTheory.Jacobson.Ideal`

`I.jacobson` is the infimum of the maximal ideals that contain `I`, for a possibly noncommutative `Ring`. `Ideal.jacobson_bot` links it with `Ring.jacobson R`, and `Ring.mem_jacobson_iff : x ∈ Ring.jacobson R ↔ ∀ y, IsUnit (x * y + 1)` is the theorem (replace `y` by `-y`). `Ideal.mem_jacobson_iff` is the form for `I.jacobson`, and `Ideal.radical_le_jacobson` gives $\sqrt{I} \subseteq J(I)$.

<?decl Ideal.jacobson?>
:::

### Examples

**Example (The nilradical of $\mathbb{Z}/360$).** The ideals of $\mathbb{Z}/360$ are the $(d)/(360)$ with $d \mid 360$ (Volume 6, Chapter 2). With $360 = 2^3 \cdot 3^2 \cdot 5$, the primes are $(p)/(360)$ for $p = 2, 3, 5$, and they are all maximal. So $\mathfrak{N} = J = (30)/(360)$. Check: $30^3 = 27000 = 75 \cdot 360$, and $[30]^2 = [900] = [180] \ne 0$. The class of $12$ is not nilpotent, since $5 \nmid 12^n$.

**Example (Radicals in $\mathbb{Z}$ and $k[x]$).** In $\mathbb{Z}$, $\sqrt{(n)} = (p_1 \cdots p_r)$ for $n = p_1^{e_1} \cdots p_r^{e_r}$, by the same argument. So $\sqrt{(4)} = (2) \ne (4)$, and $(4)$ is not radical. In $k[x]/(x^n)$ for a field $k$, the only prime is $(x)/(x^n)$, so $\mathfrak{N} = J = (x)/(x^n)$.

**Counterexample (The nilradical and the Jacobson radical differ).** Let $R = \mathbb{Z}_{(2)} = \{ a/b \in \mathbb{Q} : b \text{ odd} \}$. It is a domain, so $\mathfrak{N}(R) = 0$. An element $a/b$ (with $b$ odd) is a unit exactly when $a$ is odd. So the nonunits form the ideal $2R$, which is the only maximal ideal, and $J(R) = 2R \ne 0$.

### The library around it

The nilradical is in `Mathlib.RingTheory.Nilpotent.Lemmas` and the Jacobson radical in `Mathlib.RingTheory.Jacobson.Ideal`. The name `IsJacobsonRing` is a different notion, used in Chapter 6. Common errors:

- `Ideal.exists_le_prime_disjoint` takes a `Submonoid`, not a set. For the powers of `x` use `Submonoid.powers x`.
- `Ring.mem_jacobson_iff` states the unit condition with `x * y + 1`, not `1 - x * y`.

### Exercises

1. (A) Compute $\sqrt{(72)}$ in $\mathbb{Z}$ and the nilradical of $\mathbb{Z}/72$.
2. (A) Show that $1 + x$ is a unit if $x$ is nilpotent. Hint: $(1 + x)(1 - x + x^2 - \dots \pm x^{n - 1}) = 1 \pm x^n$.
3. (B) Show that $R / \sqrt{I}$ is reduced, and that $\sqrt{I}$ is the smallest radical ideal that contains $I$.
4. (B) Show that $\mathfrak{N}(R)$ is prime if and only if $R$ has exactly one minimal prime.
5. (B) Let $k$ be a field. Show $J(k[x]) = 0$. Hint: if $f \ne 0$ lies in $J$, then $1 - x f$ has degree at least $1$.
6. (C) Suppose each $x \in R$ satisfies $x^n = x$ for some $n \ge 2$ that depends on $x$. Show $J(R) = 0$. Hint: for $x \in J(R)$, $e = x^{n - 1}$ is idempotent, and $1 - e$ is a unit with $e (1 - e) = 0$.
7. (C) Let $P$ be a minimal prime of $R$ and $x \in P$. Show that $s x^n = 0$ for some $s \notin P$ and some $n$. Hint: apply the theorem on multiplicative sets to $S = \{ s x^n : s \notin P, n \ge 0 \}$ and the ideal $0$.

### Notes and history

The Jacobson radical takes its name from Nathan Jacobson, who studied it for noncommutative rings. Atiyah and Macdonald, Chapter 1, give the proofs of this section in the same form.

### Reference

<?reference?>
