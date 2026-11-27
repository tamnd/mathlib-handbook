---
title: Local rings and residue fields
kind: theory
modules:
  - Mathlib.RingTheory.LocalRing.Defs
  - Mathlib.RingTheory.LocalRing.Basic
  - Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
  - Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
  - Mathlib.RingTheory.LocalRing.ResidueField.Defs
  - Mathlib.RingTheory.LocalRing.RingHom.Basic
explains:
  E3: [IsLocalRing, IsLocalRing.maximalIdeal, IsLocalRing.ResidueField, IsLocalRing.of_isUnit_or_isUnit_one_sub_self, IsLocalRing.local_hom_tfae]
  E2: [IsLocalRing.mem_maximalIdeal, IsLocalRing.residue, IsLocalRing.isUnit_or_isUnit_one_sub_self, IsLocalRing.nonunits_add, IsLocalRing.of_unique_max_ideal, IsLocalRing.jacobson_eq_maximalIdeal, Field.instIsLocalRing, IsLocalRing.ResidueField.lift, IsLocalRing.of_surjective']
  E1: auto
families: []
requires: [V06, V10.C01]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Local rings and residue fields

### Overview

A local ring has one maximal ideal $\mathfrak m$. Then every element outside $\mathfrak m$ is a unit, and the ring has a single residue field $k = R/\mathfrak m$. In geometry, the local ring of a variety at a point consists of the rational functions that are defined at the point, the maximal ideal consists of those that vanish there, and the residue field is the field of values. In arithmetic, the ring $\mathbb{Z}_{(p)}$ keeps only the prime $p$ of $\mathbb{Z}$: all other primes become units.

The section proves the criteria for a ring to be local (the nonunits form an ideal; for each $a$, one of $a$ and $1 - a$ is a unit), defines local homomorphisms, and proves that the localization $R_{\mathfrak p}$ of any ring at a prime ideal $\mathfrak p$ is local, with residue field the fraction field of $R/\mathfrak p$.

### Definitions

**Definition (Local ring).** A commutative ring $R$ is local if it has exactly one maximal ideal $\mathfrak m$. The residue field of $R$ is the field $k = R/\mathfrak m$. One writes $(R, \mathfrak m)$ or $(R, \mathfrak m, k)$ for a local ring.

*Remarks.* A local ring is not the zero ring, since the zero ring has no maximal ideal. A field is local with $\mathfrak m = 0$. The word "local" has nothing to do with a topology here. It comes from the local rings of a variety at a point.

::: mathlib
`IsLocalRing` · `Mathlib.RingTheory.LocalRing.Defs`

`IsLocalRing R` is a class that extends `Nontrivial R` with one field, `isUnit_or_isUnit_of_add_one : a + b = 1 → IsUnit a ∨ IsUnit b`. So the definition in Mathlib is criterion 4 of the theorem below, not "one maximal ideal". This form makes sense in a semiring and in a noncommutative ring, and it is a statement about elements, which is easy to check. `IsLocalRing.of_unique_max_ideal` gives the class from the textbook definition.

<?decl IsLocalRing?>
:::

::: mathlib
`IsLocalRing.maximalIdeal` · `Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs`

The maximal ideal is defined as the set `nonunits R` with an ideal structure. So `IsLocalRing.mem_maximalIdeal x : x ∈ maximalIdeal R ↔ x ∈ nonunits R` holds by definition. The instance `IsLocalRing.maximalIdeal.isMaximal` says that it is maximal, and `IsLocalRing.maximal_ideal_unique` that it is the only one.

<?decl IsLocalRing.maximalIdeal?>
:::

::: mathlib
`IsLocalRing.ResidueField` · `Mathlib.RingTheory.LocalRing.ResidueField.Defs`

`ResidueField R` is the quotient `R ⧸ maximalIdeal R`, with a `Field` instance, and `IsLocalRing.residue R : R →+* ResidueField R` is the quotient map.

<?decl IsLocalRing.ResidueField?>
:::

**Definition (Local homomorphism).** Let $f : R \to S$ be a ring map. Then $f$ is local if every $a \in R$ with $f(a)$ a unit of $S$ is a unit of $R$.

Every ring map sends units to units. A local map also reflects them. For local rings this means that $f$ sends the maximal ideal into the maximal ideal, as the theorem below proves.

::: mathlib
`IsLocalHom` · `Mathlib.Algebra.Group.Units.Hom`

The class `IsLocalHom f` has the field `map_nonunit : IsUnit (f a) → IsUnit a`. It is defined for any map of monoids, in Volume 5. Since it is a class, Mathlib states theorems about local maps with `[IsLocalHom f]`, and instances provide it for surjections onto a local ring and for the residue map.

<?decl IsLocalHom?>
:::

### Theorems and proofs

**Theorem (Criteria for a local ring).** Let $R$ be a nonzero commutative ring. The following are equivalent:

1. $R$ is local;
2. the set of nonunits of $R$ is an ideal;
3. for every $a \in R$, $a$ or $1 - a$ is a unit;
4. for all $a, b \in R$ with $a + b = 1$, $a$ or $b$ is a unit.

When they hold, the maximal ideal is the set of nonunits.

*Proof.* $1 \Rightarrow 2$. Let $\mathfrak m$ be the maximal ideal. A unit does not lie in a proper ideal, so $\mathfrak m$ consists of nonunits. A nonunit $a$ generates a proper ideal $(a)$, and every proper ideal lies in a maximal ideal by Krull's theorem (Volume 6, Chapter 2). So $a \in \mathfrak m$. Hence $\mathfrak m$ is the set of nonunits.

$2 \Rightarrow 3$. If $a$ and $1 - a$ are both nonunits, their sum $1$ lies in the ideal of nonunits, which is absurd.

$3 \Rightarrow 4$. Put $b = 1 - a$.

$4 \Rightarrow 1$. Let $N$ be the set of nonunits. Then $0 \in N$, as $R \ne 0$. If $a \in N$ and $r \in R$, then $ra \in N$: if $ra$ is a unit with inverse $u$, then $a \cdot (ru) = 1$ and $a$ is a unit. If $a, b \in N$ and $a + b$ is a unit $u$, then $au^{-1} + bu^{-1} = 1$, so by 4 one of $au^{-1}$ and $bu^{-1}$ is a unit, and then $a$ or $b$ is a unit, a contradiction. So $N$ is an ideal, and it is proper since $1 \notin N$. Every proper ideal consists of nonunits, so it lies in $N$. Hence $N$ is a maximal ideal, and it is the only one. $\square$

::: mathlib
`IsLocalRing.of_isUnit_or_isUnit_one_sub_self` · `Mathlib.RingTheory.LocalRing.Basic`

Criterion 3 as a constructor of the class, for any nontrivial ring. The converse is `IsLocalRing.isUnit_or_isUnit_one_sub_self`. Criterion 2 is `IsLocalRing.nonunits_add`, and the constructor from it is `IsLocalRing.of_nonunits_add`.

<?decl IsLocalRing.of_isUnit_or_isUnit_one_sub_self?>
:::

**Corollary.** In a local ring $(R, \mathfrak m)$, $1 + x$ is a unit for every $x \in \mathfrak m$, and the Jacobson radical of $R$ is $\mathfrak m$.

*Proof.* If $1 + x$ were a nonunit, it would lie in $\mathfrak m$, and then $1 = (1 + x) - x \in \mathfrak m$. The Jacobson radical is the intersection of the maximal ideals, here only $\mathfrak m$. $\square$

**Theorem (Local homomorphisms).** Let $f : (R, \mathfrak m_R) \to (S, \mathfrak m_S)$ be a ring map of local rings. The following are equivalent: (a) $f$ is local; (b) $f(\mathfrak m_R) \subseteq \mathfrak m_S$; (c) $f^{-1}(\mathfrak m_S) = \mathfrak m_R$. A local map induces a map of residue fields $R/\mathfrak m_R \to S/\mathfrak m_S$.

*Proof.* (a) $\Rightarrow$ (b). If $a \in \mathfrak m_R$, then $a$ is not a unit, so $f(a)$ is not a unit, so $f(a) \in \mathfrak m_S$. (b) $\Rightarrow$ (c). By (b), $\mathfrak m_R \subseteq f^{-1}(\mathfrak m_S)$. The right side is a proper ideal, since it does not contain $1$, and $\mathfrak m_R$ is maximal, so they are equal. (c) $\Rightarrow$ (a). If $f(a)$ is a unit, then $f(a) \notin \mathfrak m_S$, so $a \notin f^{-1}(\mathfrak m_S) = \mathfrak m_R$, and $a$ is a unit. For the last claim, the composite $R \to S \to S/\mathfrak m_S$ has kernel $f^{-1}(\mathfrak m_S) = \mathfrak m_R$, so it factors through $R/\mathfrak m_R$. $\square$

::: mathlib
`IsLocalRing.local_hom_tfae` · `Mathlib.RingTheory.LocalRing.RingHom.Basic`

The equivalence as a `List.TFAE` with five entries, among them `IsLocalHom f`, `Ideal.map f (maximalIdeal R) ≤ maximalIdeal S` and `(maximalIdeal S).comap f = maximalIdeal R`. A single implication is extracted with `(IsLocalRing.local_hom_tfae f).out 0 2`. The map of residue fields is `IsLocalRing.ResidueField.map`.

<?decl IsLocalRing.local_hom_tfae?>
:::

**Theorem (Localization at a prime).** Let $R$ be a commutative ring, $\mathfrak p$ a prime ideal and $S = R \setminus \mathfrak p$. Then $R_{\mathfrak p} = S^{-1}R$ is a local ring with maximal ideal $\mathfrak p R_{\mathfrak p} = \{a/s : a \in \mathfrak p, s \in S\}$.

*Proof.* Let $x = a/s \in R_{\mathfrak p}$. If $a \notin \mathfrak p$, then $a \in S$, and $s/a$ is an inverse of $x$. If $a \in \mathfrak p$, then $x$ is not a unit. Indeed, assume $(a/s)(b/t) = 1$. Then there is $u \in S$ with $u(ab - st) = 0$, so $ust = uab \in \mathfrak p$. But $u$, $s$ and $t$ lie in $S$, and $S$ is closed under products since $\mathfrak p$ is prime, so $ust \notin \mathfrak p$. This is a contradiction. So the nonunits of $R_{\mathfrak p}$ are exactly the fractions $a/s$ with $a \in \mathfrak p$. These form the ideal $\mathfrak p R_{\mathfrak p}$, which is proper. By criterion 2, $R_{\mathfrak p}$ is local with this maximal ideal. $\square$

The residue field of $R_{\mathfrak p}$ is the field of fractions of the domain $R/\mathfrak p$: the map $a/s \mapsto \bar a/\bar s$ from $R_{\mathfrak p}$ to $\operatorname{Frac}(R/\mathfrak p)$ is surjective with kernel $\mathfrak p R_{\mathfrak p}$. For $\mathfrak p$ maximal it is $R/\mathfrak p$ itself.

::: mathlib
`Localization.AtPrime.isLocalRing` · `Mathlib.RingTheory.Localization.AtPrime.Basic`

The instance `IsLocalRing (Localization.AtPrime P)` for a prime `P`, in a module of Volume 9, Commutative algebra I. `Localization.AtPrime P` abbreviates `Localization P.primeCompl`, where `P.primeCompl` is the submonoid $R \setminus P$. The map `algebraMap R (Localization.AtPrime P)` is not local in general: elements outside `P` that are nonunits of `R` become units.

<?decl Localization.AtPrime.isLocalRing?>
:::

### Examples

**Example ($\mathbb{Z}_{(p)}$).** For a prime $p$, the localization $\mathbb{Z}_{(p)} = \{a/b \in \mathbb{Q} : p \nmid b\}$ is local with maximal ideal $p\mathbb{Z}_{(p)} = \{a/b : p \mid a,\ p \nmid b\}$ and residue field $\mathbb{F}_p$. Every nonzero element is $p^n u$ with $u$ a unit: write $a = p^n a'$ with $p \nmid a'$, and $u = a'/b$. The integer $6$ is a unit in $\mathbb{Z}_{(5)}$ and not in $\mathbb{Z}_{(3)}$. The inclusion $\mathbb{Z}_{(p)} \to \mathbb{Q}$ is not local, since $p$ becomes a unit. The quotient map $\mathbb{Z}_{(p)} \to \mathbb{F}_p$ is local.

**Example (Power series).** Let $k$ be a field. A power series $f = \sum_{n \ge 0} a_n X^n \in k[[X]]$ with $a_0 \ne 0$ is a unit. The inverse $g = \sum b_n X^n$ must satisfy $a_0 b_0 = 1$ and $\sum_{i=0}^n a_i b_{n-i} = 0$ for $n \ge 1$, and these equations determine $b_0 = a_0^{-1}$ and then
$$b_n = -a_0^{-1}\left(a_1 b_{n-1} + \cdots + a_n b_0\right)$$
by recursion. For example $(1 - X)^{-1} = 1 + X + X^2 + \cdots$. A series with $a_0 = 0$ is $X g$ and is not a unit. So the nonunits form the ideal $(X)$, and $k[[X]]$ is local with residue field $k$, by criterion 2.

**Example (Not local).** The ring $\mathbb{Z}$ has the maximal ideals $(2)$ and $(3)$, and $3 + (-2) = 1$ with neither $3$ nor $-2$ a unit. The product $k \times k$ of two fields has $(1, 0) + (0, 1) = (1, 1)$, and neither summand is a unit. The polynomial ring $k[X]$ is not local: $X + (1 - X) = 1$.

**Example (Artinian local rings).** The ring $k[X]/(X^n)$ is local with maximal ideal $(X)$: an element $a_0 + a_1 X + \cdots$ with $a_0 \ne 0$ is a unit, since $a_0^{-1}(\text{element}) = 1 - y$ with $y$ nilpotent, and $1 - y$ has the inverse $1 + y + \cdots + y^{n-1}$. In the same way $\mathbb{Z}/p^n$ is local with maximal ideal $(p)$. A ring whose prime ideals reduce to one, such as these, is local.

### The library around it

The folder `Mathlib/RingTheory/LocalRing/` contains the theory. The lemmas are in the namespace `IsLocalRing`, and most take the ring as an explicit or implicit argument after `[IsLocalRing R]`. The instance `Field.instIsLocalRing` makes every field local. The lemma `IsLocalRing.of_surjective'` says that a nonzero quotient of a local ring is local. The lemma `IsLocalRing.jacobson_eq_maximalIdeal` gives the Jacobson radical of every proper ideal. The universal property of the residue field is `IsLocalRing.ResidueField.lift`: a local map from `R` to a field factors through the residue field.

Common errors of a learner:

- `IsLocalRing R` is a class on the type. A local ring that arises as `Localization.AtPrime P` gets the class by instance search, but a ring that is local by a theorem needs `haveI` or a named instance.
- The map `algebraMap R (Localization.AtPrime P)` is not local. Its composite with the residue field is the map to the fraction field of `R ⧸ P`.
- A ring map between local rings need not be local. Check `IsLocalHom` before a theorem that needs it.

### Exercises

1. (A) Show that $\mathbb{Z}/n$ is local if and only if $n$ is a power of a prime.
2. (A) Show that $\mathbb{Z}_{(p)}$ is a PID whose nonzero ideals are $p^n \mathbb{Z}_{(p)}$.
3. (A) Let $(R, \mathfrak m)$ be local and $e$ an idempotent. Show that $e = 0$ or $e = 1$.
4. (B) Show that a ring $R$ is local if and only if $R \ne 0$ and the set of nonunits is closed under addition.
5. (B) Let $R$ be a ring in which every element is a unit or nilpotent. Show that $R$ is local. Give an example that is not a field and not of the form $k[X]/(X^n)$.
6. (B) Let $(R, \mathfrak m)$ be local. Show that the power series ring $R[[X]]$ is local with maximal ideal $(\mathfrak m, X)$.
7. (B) Let $k$ be a field and $R$ the ring of rational functions $f/g \in k(X)$ with $g(0) \ne 0$. Show that $R \cong k[X]_{(X)}$, that $R$ is local, and that its residue field is $k$, the map being evaluation at $0$.
8. (C) Let $R$ be a ring and $\mathfrak p$ a prime. Show that $R_{\mathfrak p}/\mathfrak p R_{\mathfrak p}$ is isomorphic to the field of fractions of $R/\mathfrak p$, and that the primes of $R_{\mathfrak p}$ correspond to the primes of $R$ contained in $\mathfrak p$.

### Notes and history

Krull introduced local rings, under the name "Stellenringe", in 1938, and Chevalley proposed the name "local ring". The local ring of a variety at a point is the basic object of Zariski's algebraic geometry. The criteria of this section are in Atiyah and Macdonald, Chapter 1, and in Matsumura, *Commutative Ring Theory*, Section 1.

In Mathlib, local rings were renamed from `LocalRing` to `IsLocalRing`, to follow the convention that a class which is a property has a name that starts with `Is`.

### Reference

<?reference?>
