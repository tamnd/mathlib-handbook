---
title: Extensions, localizations and quotients of valuations
kind: api
modules:
  - Mathlib.RingTheory.Valuation.Extension
  - Mathlib.RingTheory.Valuation.ExtendToLocalization
  - Mathlib.RingTheory.Valuation.AlgebraInstances
  - Mathlib.RingTheory.Valuation.Algebraic
  - Mathlib.RingTheory.Valuation.Minpoly
  - Mathlib.RingTheory.Valuation.IsTrivialOn
  - Mathlib.RingTheory.Valuation.Quotient
  - Mathlib.RingTheory.Valuation.RamificationGroup
explains:
  E2: [Valuation.HasExtension, Valuation.HasExtension.val_map_le_iff, Valuation.HasExtension.mapValueGroup₀, Valuation.extendToLocalization, Valuation.onQuot, Valuation.exists_map_pow_eq_map_algebraMap_of_isAlgebraic, Valuation.coeff_zero_minpoly, Valuation.transcendental_of_ne_one, ValuationSubring.decompositionSubgroup, ValuationSubring.inertiaSubgroup]
  E1: auto
families: []
requires: [V10.C01, V10.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Extensions, localizations and quotients of valuations

### Overview

A valuation on a ring gives valuations on related rings. It extends to a localization when the inverted elements have nonzero value, and it descends to a quotient by an ideal inside its support. For an algebra $A$ over $R$, a valuation on $A$ restricts to a valuation on $R$. The pair is an extension when the restriction is equivalent to the given valuation on $R$.

This section describes the class for extensions and the maps it gives between value groups and rings of integers. It then describes extension to a localization, descent to a quotient, the values of algebraic and transcendental elements, and the decomposition and inertia subgroups of a Galois group at a valuation ring.

### The library around it

#### Extensions of valuations

Let $A$ be an $R$-algebra with valuations $v_R : R \to \Gamma_R$ and $v_A : A \to \Gamma_A$. The class `Valuation.HasExtension vR vA` in `Mathlib.RingTheory.Valuation.Extension` says that $v_R$ is equivalent to the restriction `Valuation.comap (algebraMap R A) vA`. Its field is `Valuation.HasExtension.val_isEquiv_comap`. The values in $\Gamma_R$ and $\Gamma_A$ are not compared directly, since the groups can differ. Only the order of the values is kept.

| Lean name | Statement |
|---|---|
| `Valuation.HasExtension.val_map_le_iff` | $v_A(x) \le v_A(y)$ if and only if $v_R(x) \le v_R(y)$, for $x, y \in R$ |
| `Valuation.HasExtension.val_map_lt_iff` | the same for $<$ |
| `Valuation.HasExtension.val_map_eq_iff` | the same for $=$ |
| `Valuation.HasExtension.val_map_le_one_iff` | $v_A(x) \le 1$ if and only if $v_R(x) \le 1$ |
| `Valuation.HasExtension.val_map_lt_one_iff` | $v_A(x) < 1$ if and only if $v_R(x) < 1$ |
| `Valuation.HasExtension.val_map_eq_one_iff` | $v_A(x) = 1$ if and only if $v_R(x) = 1$ |
| `Valuation.HasExtension.id` | a valuation extends itself |
| `Valuation.HasExtension.comp` | extensions compose in a tower |
| `Valuation.HasExtension.ofComapInteger` | for a field $K$, the integers of $v_A$ pull back to the integers of $v_K$ |

The last item is a useful criterion. On a field, a valuation is determined up to equivalence by its ring of integers, so it is enough to check that $x \in K$ has $v_A(x) \le 1$ if and only if $v_K(x) \le 1$.

An extension gives the map of value groups with zero `Valuation.HasExtension.mapValueGroup₀ vR vA`. It sends the value of $x$ to the value of its image, `Valuation.HasExtension.mapValueGroup₀_apply_restrict`, and it is strictly monotone, `Valuation.HasExtension.mapValueGroup₀_strictMono`. It is the only such map, by `Valuation.HasExtension.mapValueGroup₀_uniq`, and it is functorial, by `Valuation.HasExtension.mapValueGroup₀_self` and `Valuation.HasExtension.mapValueGroup₀_comp_mapValueGroup₀`. For a finite extension of fields with value groups isomorphic to $\mathbb{Z}$, the image of this map has a finite index $e$, the ramification index.

#### The map of rings of integers

The extension makes the ring of integers of $v_A$ an algebra over the ring of integers of $v_R$, by the instance `Valuation.HasExtension.instAlgebraInteger`. The lemma `Valuation.HasExtension.val_algebraMap` says that this map agrees with `algebraMap R A`. For fields $K \subseteq L$ the module gives more.

1. The ring map of valuation subrings is injective, `Valuation.HasExtension.algebraMap_injective`, and local, by `Valuation.HasExtension.instIsLocalHomSubtypeMemValuationSubringValuationSubringRingHomAlgebraMap`.
2. The maximal ideal of the larger ring lies over the maximal ideal of the smaller ring, `Valuation.HasExtension.maximalIdeal_comap_algebraMap_eq_maximalIdeal`, and `Valuation.HasExtension.algebraMap_mem_maximalIdeal_iff` is the form for one element.
3. The residue fields form an extension that commutes with the residue maps, `Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap`. Its degree is the residue degree $f$.

The module `Mathlib.RingTheory.Valuation.AlgebraInstances` treats the case of a discrete valuation $v$ on $K$ with values in $\mathbb{Z}^{m0}$. It makes $L$ an algebra over $\mathcal{O}_v$, makes the integral closure of $\mathcal{O}_v$ in $E$ an algebra over the integral closure in $L$ for a tower $K \subseteq L \subseteq E$, and proves `ValuationSubring.isIntegral_of_mem_ringOfIntegers`. The definition `ValuationSubring.equiv` identifies this integral closure with each ring $R$ that is an integral closure of $\mathcal{O}_v$ in $L$.

#### Localization and quotients

Let $v$ be a valuation on $A$ and $S$ a submonoid with $v(s) \ne 0$ for all $s \in S$, that is, $S$ is outside the support. Then $v$ extends to each localization $B = S^{-1}A$. This is `Valuation.extendToLocalization v hS B` in `Mathlib.RingTheory.Valuation.ExtendToLocalization`.

**Theorem.** The extension sends $x/s$ to $v(x)v(s)^{-1}$, and it agrees with $v$ on $A$. These are `Valuation.extendToLocalization_mk'` and `Valuation.extendToLocalization_apply_map_apply`.

*Proof.* Put $w(x/s) = v(x)v(s)^{-1}$. If $x/s = y/t$, then $u(xt - ys) = 0$ for some $u \in S$. So $v(u)v(x)v(t) = v(u)v(y)v(s)$, and $v(u) \ne 0$ in a group with zero gives $v(x)v(s)^{-1} = v(y)v(t)^{-1}$. Thus $w$ is well defined. It is multiplicative. For the sum write $x/s + y/t = (xt + ys)/st$ and use $v(xt + ys) \le \max(v(x)v(t), v(y)v(s))$. $\square$

The module `Mathlib.RingTheory.Valuation.Quotient` handles quotients. For an ideal $J$ inside the support $\operatorname{supp} v$, `Valuation.onQuot v hJ` is the valuation on $R/J$ induced by $v$, and `Valuation.onQuotVal` is its underlying function. It pulls back to $v$, `Valuation.onQuot_comap_eq`, and its support is the image of the support, `Valuation.supp_quot`. For $J = \operatorname{supp} v$ the support is $0$, `Valuation.supp_quot_supp`. So each valuation is the pullback of a valuation with support $0$ on the domain $R/\operatorname{supp} v$, and then it extends to the fraction field. The same results exist for additive valuations, such as `AddValuation.onQuot` and `AddValuation.supp_quot`.

#### Algebraic and transcendental elements

Let $K$ be a field and $A$ a $K$-algebra with a valuation $v$.

1. `Valuation.exists_map_pow_eq_map_algebraMap_of_isAlgebraic` in `Mathlib.RingTheory.Valuation.Algebraic`: if $x$ is algebraic over $K$, then $v(x)^n$ is the value of an element of $K$ for some $n$ with $0 < n \le \deg \operatorname{minpoly}_K(x)$. So the value group of an algebraic extension is torsion over the value group of $K$.
2. `Valuation.coeff_zero_minpoly` in `Mathlib.RingTheory.Valuation.Minpoly`: for $x \in K$ seen in $L$, the constant coefficient of its minimal polynomial has value $v(x)$. The lemma `Valuation.pow_coeff_zero_ne_zero_of_unit` says that a power of the value of the constant coefficient is nonzero for a unit $x$ of a finite extension.

The class `Valuation.IsTrivialOn A v` says that $v$ is $1$ on the nonzero elements of $A$, as for a valuation on $k(X)$ trivial on $k$. The module `Mathlib.RingTheory.Valuation.IsTrivialOn` proves that an element $w$ with $v(w) > 1$ has $v(p(w)) = v(w)^{\deg p}$ for each nonzero $p \in A[X]$, `Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X`. A consequence is `Valuation.transcendental_of_ne_one`: a nonzero $y$ with $v(y) \ne 1$ is transcendental over $A$. The companion `Polynomial.valuation_aeval_monomial_eq_valuation_pow` treats one monomial.

#### Decomposition and inertia subgroups

Let $L/K$ be an extension of fields and $A$ a valuation subring of $L$. The module `Mathlib.RingTheory.Valuation.RamificationGroup` defines the decomposition subgroup `ValuationSubring.decompositionSubgroup K A`, the stabilizer of $A$ in $\operatorname{Gal}(L/K)$. This group acts on $A$, by the instance `ValuationSubring.decompositionSubgroupMulSemiringAction`. The inertia subgroup `ValuationSubring.inertiaSubgroup K A` is the subgroup of the decomposition group that acts trivially on the residue field of $A$. These are the valuation forms of the groups of Section 4 of Chapter 1, where the prime $Q$ is replaced by the valuation ring $A$.

#### Common errors

1. `Valuation.HasExtension vR vA` does not say that $v_A$ extends $v_R$ as a function. The value groups can differ. Use `Valuation.HasExtension.val_map_le_iff` to compare values.
2. `Valuation.extendToLocalization` needs the proof that $S$ lies in the complement of the support. For a valuation on a domain with support $0$, this is $0 \notin S$.
3. `Valuation.onQuot` needs $J \le \operatorname{supp} v$, not $J \le \mathfrak m$. A valuation does not descend to a quotient by an ideal with elements of nonzero value.

### Exercises

1. (A) Let $v$ be the $p$-adic valuation on $\mathbb{Z}$. Describe `Valuation.extendToLocalization` for $S = \mathbb{Z} \setminus p\mathbb{Z}$ and for $S = \mathbb{Z} \setminus \{0\}$.
2. (A) Show that the valuation $v(x) = 2^{-\operatorname{ord}_2(x)}$ on $\mathbb{Q}(\sqrt 2)$, with $\operatorname{ord}_2(\sqrt 2) = 1/2$, extends the $2$-adic valuation of $\mathbb{Q}$, and find the ramification index.
3. (B) Prove `Valuation.HasExtension.comp`: an extension of an extension is an extension.
4. (B) Let $v$ be a valuation on $k(X)$ trivial on $k$ with $v(X) > 1$. Show that $v(p) = v(X)^{\deg p}$ for each nonzero polynomial $p$, so $v$ is the valuation at infinity.
5. (B) Let $v$ be a valuation on $R$. Show that $\operatorname{supp} v$ is a prime ideal and that `Valuation.onQuot` gives a valuation on the domain $R / \operatorname{supp} v$ with support $0$.
6. (C) Use `Valuation.exists_map_pow_eq_map_algebraMap_of_isAlgebraic` to show that for a finite extension $L/K$ of valued fields, the index of $\Gamma_K$ in $\Gamma_L$ is at most $[L : K]$ when $\Gamma_L$ is cyclic.

### Reference

<?reference?>
