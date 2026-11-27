---
title: Valuation rings
kind: theory
modules:
  - Mathlib.RingTheory.Valuation.ValuationRing
  - Mathlib.RingTheory.Valuation.ValuationSubring
  - Mathlib.RingTheory.Valuation.Integral
  - Mathlib.RingTheory.Valuation.LocalSubring
explains:
  E3: [ValuationRing, ValuationSubring, ValuationRing.tfae, LocalSubring.exists_le_valuationSubring, Valuation.Integers.isIntegrallyClosed]
  E2: [ValuationRing.iff_dvd_total, ValuationRing.iff_ideal_total, ValuationRing.isLocalRing, ValuationRing.iff_local_bezout_domain, ValuationRing.ValueGroup, ValuationRing.valuation, ValuationRing.of_integers, ValuationSubring.mem_or_inv_mem, ValuationSubring.valuation, LocalSubring.isMax_iff, iInf_valuationSubring_superset]
  E1: auto
families: []
requires: [V10.C01, V10.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Valuation rings

### Overview

Section 1 attached to a valuation $v$ on a field $K$ its ring of integers $\mathcal{O}_v$, a subring with the property that $x \in \mathcal{O}_v$ or $x^{-1} \in \mathcal{O}_v$ for each $x \ne 0$. This section starts from that property. A domain with it is a valuation ring, and every valuation ring is the ring of integers of a valuation, built from divisibility. Valuation rings are local and integrally closed, and their ideals form a chain.

The main theorem is the extension theorem: every local subring of a field $K$ lies under a valuation ring of $K$, with the maximal ideals compatible. As a consequence, the integral closure of a subring of $K$ is the intersection of the valuation rings of $K$ that contain it. This is the bridge between integrality (Chapter 1) and valuations.

### Definitions

**Definition (Valuation ring).** A domain $A$ with field of fractions $K$ is a valuation ring if for every $x \in K^\times$, $x \in A$ or $x^{-1} \in A$. A valuation subring of a field $K$ is a subring $A \subseteq K$ such that for every $x \in K^\times$, $x \in A$ or $x^{-1} \in A$.

A field is a valuation ring. A valuation subring of $K$ is a valuation ring with fraction field $K$: if $x \in K$ and $x \notin A$, then $x^{-1} \in A$ and $x = 1/x^{-1}$.

::: mathlib
`ValuationRing` · `Mathlib.RingTheory.Valuation.ValuationRing`

`ValuationRing A` is a class on a domain `A`, defined without the fraction field: it extends `PreValuationRing A`, whose field says that for all `a b : A` there is `c` with `a * c = b` or `b * c = a`. So the definition in Mathlib is "divisibility is total", the second condition of the theorem below. The other forms are in `ValuationRing.tfae`.

<?decl ValuationRing?>
:::

::: mathlib
`ValuationSubring` · `Mathlib.RingTheory.Valuation.ValuationSubring`

`ValuationSubring K` is a structure that extends `Subring K` by the field `mem_or_inv_mem' : ∀ x, x ∈ A ∨ x⁻¹ ∈ A`. The subrings form a complete lattice, and `ValuationSubring.mem_or_inv_mem` is the defining property. The instance `ValuationSubring.instValuationRingSubtypeMem` makes each one a valuation ring.

<?decl ValuationSubring?>
:::

**Definition (Value group of a valuation ring).** Let $A$ be a valuation ring with fraction field $K$. The value group is $\Gamma_A = K^\times / A^\times$, ordered by $xA^\times \le yA^\times$ if $y/x \in A$. The valuation of $A$ is the map $v_A : K \to \Gamma_A \cup \{0\}$, $v_A(x) = xA^\times$ for $x \ne 0$, with the order reversed so that elements of $A$ have value at most $1$.

### Theorems and proofs

**Theorem (Characterizations).** Let $A$ be a domain with field of fractions $K$. The following are equivalent:

1. $A$ is a valuation ring;
2. for all $a, b \in A$, $a \mid b$ or $b \mid a$;
3. the ideals of $A$ are totally ordered by inclusion;
4. $A$ is local and every finitely generated ideal of $A$ is principal.

*Proof.* $1 \Rightarrow 2$. If $a = 0$ or $b = 0$, one divides the other. Otherwise $b/a \in A$ or $a/b \in A$. $2 \Rightarrow 1$. Let $x = b/a \in K^\times$ with $a, b \in A$. If $a \mid b$ then $x \in A$, and if $b \mid a$ then $x^{-1} \in A$.

$2 \Rightarrow 3$. Let $I, J$ be ideals with $I \not\subseteq J$. Take $a \in I \setminus J$, and let $b \in J$. By 2, $a \mid b$ or $b \mid a$. The case $b \mid a$ gives $a \in (b) \subseteq J$, which is false. So $a \mid b$ for every $b \in J$, and $J \subseteq (a) \subseteq I$. $3 \Rightarrow 2$. The ideals $(a)$ and $(b)$ are comparable.

$3 \Rightarrow 4$. The maximal ideals are comparable, so there is only one, and $A$ is local. A finitely generated ideal $(a_1, \ldots, a_n)$ is the sum of the chain $(a_1), \ldots, (a_n)$, so it is the largest of them. $4 \Rightarrow 2$. Let $a, b \in A$, not both zero, and $(a, b) = (d)$. Write $a = d a'$, $b = d b'$ and $d = ra + sb$. Cancel $d$: $1 = ra' + sb'$. Since $A$ is local, $ra'$ or $sb'$ is a unit, so $a'$ or $b'$ is a unit. If $a'$ is a unit, then $a = da'$ divides $b = d b'$. $\square$

::: mathlib
`ValuationRing.tfae` · `Mathlib.RingTheory.Valuation.ValuationRing`

The four conditions as a `List.TFAE` for a domain `R`, with the first one stated through `FractionRing R` and `IsLocalization.IsInteger`. Condition 2 is `ValuationRing.iff_dvd_total`, condition 3 is `ValuationRing.iff_ideal_total`, and condition 4 is `ValuationRing.iff_local_bezout_domain`, with Bézout meaning that finitely generated ideals are principal. The instance `ValuationRing.isLocalRing` makes each valuation ring local.

<?decl ValuationRing.tfae?>
:::

**Theorem (Valuation rings and valuations).** Let $A$ be a valuation ring with field of fractions $K$. Then $\Gamma_A$ is a linearly ordered group, $v_A$ is a valuation on $K$, and its ring of integers is $A$. Conversely, the ring of integers of a valuation on $K$ is a valuation subring of $K$.

*Proof.* The relation $xA^\times \le yA^\times$ is well defined and is an order, compatible with products. Antisymmetry: if $y/x$ and $x/y$ lie in $A$, then $y/x$ is a unit. Totality is condition 1. For the valuation axioms, $v_A$ is multiplicative by definition. For the ultrametric inequality, let $x, y \ne 0$ and assume $y/x \in A$. Then $x + y = x(1 + y/x)$ with $1 + y/x \in A$, so $x + y$ is a multiple of $x$ by an element of $A$, which is the inequality. The ring of integers of $v_A$ is the set of $x$ with $x/1 \in A$, that is $A$. The converse is the theorem on rings of integers in Section 1. $\square$

::: mathlib
`ValuationRing.valuation` · `Mathlib.RingTheory.Valuation.ValuationRing`

`ValuationRing.valuation A K : Valuation K (ValuationRing.ValueGroup A K)`, for a valuation ring `A` with fraction field `K`. The value group is the quotient of `K` by the action of the units of `A`, with zero included. The converse direction is `ValuationRing.of_integers`: if `v.Integers O`, then `O` is a valuation ring. For a valuation subring, `ValuationSubring.valuation` is the valuation with the same construction.

<?decl ValuationRing.valuation?>
:::

**Theorem (Integrally closed).** A valuation ring is integrally closed.

*Proof.* Let $A$ be a valuation ring with fraction field $K$, and $x \in K$ integral over $A$, with $x^n + a_{n-1} x^{n-1} + \cdots + a_0 = 0$, $a_i \in A$. If $x \notin A$, then $y = x^{-1} \in A$ and $y$ lies in the maximal ideal, since $y$ is not a unit of $A$. Multiply the equation by $y^{n}$:
$$1 = -(a_{n-1} y + a_{n-2} y^2 + \cdots + a_0 y^n).$$
The right side lies in the maximal ideal, since each term has a factor $y$. This is a contradiction. $\square$

::: mathlib
`Valuation.Integers.isIntegrallyClosed` · `Mathlib.RingTheory.Valuation.Integral`

If `O` is the ring of integers of a valuation on a field `K`, in the sense `v.Integers O`, then `IsIntegrallyClosed O`. Combined with `ValuationRing.valuation`, every valuation ring is integrally closed.

<?decl Valuation.Integers.isIntegrallyClosed?>
:::

A local ring $B$ dominates a local ring $A$ if $A \subseteq B$ and $\mathfrak m_A = A \cap \mathfrak m_B$, that is the inclusion is a local homomorphism (Chapter 2, Section 1).

**Theorem (Extension theorem).** Let $K$ be a field and $A \subseteq K$ a local subring. There is a valuation subring $V$ of $K$ that dominates $A$.

*Proof sketch.* The local subrings of $K$ that dominate $A$ form a set ordered by domination, and the union of a chain is again a local subring that dominates every member. By Zorn's lemma there is a maximal element $(B, \mathfrak m_B)$. It remains to show that $B$ is a valuation ring. Let $x \in K^\times$. Assume first that $\mathfrak m_B B[x] \ne B[x]$. Then there is a maximal ideal $\mathfrak n$ of $B[x]$ containing $\mathfrak m_B$, and the local ring $B[x]_{\mathfrak n}$ dominates $B$, so it equals $B$ by maximality and $x \in B$. Otherwise $\mathfrak m_B B[x] = B[x]$, and in the same way, if $\mathfrak m_B B[x^{-1}] \ne B[x^{-1}]$, then $x^{-1} \in B$. It remains to rule out that both equalities hold. If they do, write $1 = \sum_{i=0}^n a_i x^i$ and $1 = \sum_{j=0}^m b_j x^{-j}$ with $a_i, b_j \in \mathfrak m_B$, and $n$, $m$ least, with $n \ge m$ by symmetry. Since $1 - b_0$ is a unit of $B$, the second equation gives $1 = \sum_{j \ge 1} c_j x^{-j}$ with $c_j \in \mathfrak m_B$. Multiply by $x^n$ to get $x^n = \sum_{j=1}^m c_j x^{n-j}$, and substitute in the first equation. This gives an equation of the same form with degree less than $n$, a contradiction. $\square$

::: mathlib
`LocalSubring.exists_le_valuationSubring` · `Mathlib.RingTheory.Valuation.LocalSubring`

For `A : LocalSubring K`, there is `B : ValuationSubring K` with `A ≤ B.toLocalSubring`. The order on `LocalSubring K` is domination: `A ≤ B` means inclusion with `IsLocalHom` on the inclusion map. The lemma `LocalSubring.isMax_iff` says that the maximal local subrings are exactly the valuation subrings.

<?decl LocalSubring.exists_le_valuationSubring?>
:::

**Corollary (Integral closure by valuations).** Let $K$ be a field and $A \subseteq K$ a subring. The integral closure of $A$ in $K$ is the intersection of the valuation subrings of $K$ that contain $A$.

*Proof sketch.* A valuation subring $V \supseteq A$ is integrally closed in $K$ by the theorem above, so it contains the integral closure. Conversely, let $x \in K$ be not integral over $A$, and $y = x^{-1}$, which is nonzero. Then $x \notin A[y]$: if $x = \sum_{i=0}^n a_i y^i$, multiply by $x^n$ to get a monic equation for $x$. So $y$ is not a unit of $A[y]$, and lies in a maximal ideal $\mathfrak n$. A valuation subring $V$ that dominates $A[y]_{\mathfrak n}$ has $y \in \mathfrak m_V$, so $x = y^{-1} \notin V$. $\square$

::: mathlib
`iInf_valuationSubring_superset` · `Mathlib.RingTheory.Valuation.LocalSubring`

For a set `s ⊆ K`, the infimum of the valuation subrings that contain `s` is the integral closure in `K` of the subring generated by `s`.

<?decl iInf_valuationSubring_superset?>
:::

### Examples

**Example (Discrete examples).** The rings $\mathbb{Z}_{(p)}$, $k[X]_{(X)}$ and $k[[X]]$ are valuation rings, the rings of integers of $v_p$, $v_0$ and the order of a power series. Their value group is $\mathbb{Z}$, and they are the discrete valuation rings of Section 3.

**Example (Not a valuation ring).** The ring $\mathbb{Z}$ is not a valuation ring: $2 \nmid 3$ and $3 \nmid 2$. The local ring $k[X, Y]_{(X, Y)}$ is not a valuation ring: neither of $X/Y$ and $Y/X$ lies in it, since $X \nmid Y$ and $Y \nmid X$. Its ideals $(X)$ and $(Y)$ are not comparable. The ring $\mathbb{Z}[\sqrt{-3}]_{(2, 1 + \sqrt{-3})}$ is local and not integrally closed, since $(1 + \sqrt{-3})/2$ is integral, so it is not a valuation ring.

**Example (A non-Noetherian valuation ring).** Let $K = \bigcup_n k((X^{1/n}))$, the field of Puiseux series, and $v$ the valuation with $v(X^q) = q$ for $q \in \mathbb{Q}$, in additive form. The ring of integers $A$ has value group $\mathbb{Q}$. Its maximal ideal is $\{v > 0\}$, and $\mathfrak m = \mathfrak m^2$: each $X^q$ with $q > 0$ is $X^{q/2} \cdot X^{q/2}$. So $\mathfrak m$ is not finitely generated, by Nakayama's lemma, and $A$ is not Noetherian.

**Example (Valuations over a point of the plane).** Over the local ring $A = k[X, Y]_{(X, Y)}$, with $K = k(X, Y)$, the rank-2 valuation $w$ of Section 1 has a ring of integers that dominates $A$. The valuation $\operatorname{ord}$, the order of vanishing at the origin (the least total degree of a monomial), also dominates $A$. The extension theorem gives one such ring, and this example shows that it is not unique.

### The library around it

The files `ValuationRing.lean` (the class and the characterizations), `ValuationSubring.lean` (subrings of a field, with the valuation and the order between subrings), `Integral.lean` (integrally closed) and `LocalSubring.lean` (domination and the extension theorem) form the theory. The lemma `IsLocalRing.exists_factor_valuationRing` in the last file states the extension theorem for a local ring map to a field. For valuation subrings, `ValuationSubring.valuation_le_one`, `ValuationSubring.valuation_eq_one_iff` and `ValuationSubring.valuation_lt_one_iff` describe the elements, the units and the maximal ideal by their values.

Common errors of a learner:

- `ValuationRing A` is a class on a type, while `ValuationSubring K` is a structure whose terms are subrings. Use the second when the field is fixed and many valuation rings are compared.
- The definition in Mathlib is total divisibility. To get "x or x⁻¹" use `ValuationRing.tfae` or `ValuationRing.isInteger_or_isInteger`.
- The order on `LocalSubring K` is domination, not inclusion.

### Exercises

1. (A) Show that the ideals of $\mathbb{Z}_{(p)}$ form the chain $\mathbb{Z}_{(p)} \supset (p) \supset (p^2) \supset \cdots \supset 0$.
2. (A) Show that a valuation ring that is Noetherian is a PID.
3. (A) Let $A$ be a valuation ring and $\mathfrak p$ a prime. Show that $A/\mathfrak p$ and $A_{\mathfrak p}$ are valuation rings.
4. (B) Let $A \subseteq B \subseteq K$ with $A$ a valuation subring. Show that $B$ is a valuation subring and that $B = A_{\mathfrak p}$ for a prime $\mathfrak p$ of $A$.
5. (B) Show that the prime ideals of a valuation ring form a chain, and that the radical of a principal ideal is prime.
6. (B) Find a valuation subring of $\mathbb{Q}(i)$ that contains $\mathbb{Z}[i]$ and whose maximal ideal contains $1 + i$.
7. (B) Show that a valuation ring is a GCD domain: every pair of elements has a greatest common divisor.
8. (C) Show that the valuation subrings of $\mathbb{Q}$ are $\mathbb{Q}$ and the rings $\mathbb{Z}_{(p)}$.

### Notes and history

Krull introduced valuation rings for general ordered groups in 1932. The extension theorem in the form with local rings and domination is due to Chevalley. The corollary on integral closures is in Atiyah and Macdonald, Corollary 5.22, and in Matsumura, *Commutative Ring Theory*, Theorem 10.4. The proof of the extension theorem in this section follows Atiyah and Macdonald, Theorem 5.21, adapted to local rings.

### Reference

<?reference?>
