---
title: Examples, subgroups and the null subgroup
kind: api
modules:
  - Mathlib.Analysis.Normed.Group.Real
  - Mathlib.Analysis.Normed.Group.Int
  - Mathlib.Analysis.Normed.Group.Rat
  - Mathlib.Analysis.Normed.Group.AddCircle
  - Mathlib.Analysis.Normed.Group.Subgroup
  - Mathlib.Analysis.Normed.Group.Submodule
  - Mathlib.Analysis.Normed.Group.NullSubmodule
  - Mathlib.Analysis.Normed.Group.SeparationQuotient
  - Mathlib.Analysis.Normed.Order.Lattice
  - Mathlib.Analysis.Normed.Order.UpperLower
  - Mathlib.Analysis.Normed.Module.TransferInstance
  - Mathlib.Analysis.Normed.Module.Shrink
  - Mathlib.Analysis.Normed.Field.TransferInstance
  - Mathlib.Analysis.Normed.Ring.TransferInstance
explains:
  E2: [Real.norm_eq_abs, AddCircle.norm_eq, AddCircle.norm_le_half_period, mem_nullSubmodule_iff, isClosed_nullSubmodule, SeparationQuotient.norm_normedMk_eq_one, norm_abs_sub_abs, dist_inf_sup]
  E1: auto
families: []
requires: [V04, V07, V13, V15]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Examples, subgroups and the null subgroup

### Overview

The first normed groups of a course are the integers, the rationals and the reals with the absolute value. A first quotient is the circle $\mathbb{R}/p\mathbb{Z}$ with the distance to the nearest point of the lattice. This section shows how Mathlib gives these examples their norms, and how it puts norms on subgroups and submodules.

A seminorm can vanish at nonzero points. These points form a closed subgroup, the null subgroup, and the quotient by it is the separation quotient of the metric. The section describes this quotient as a normed group. It then treats normed lattices, where the norm is compatible with the order, and the order properties of the distance on $\mathbb{R}^n$. It ends with the tool that moves a norm along a bijection of types.

### The library around it

#### The numbers

The norm on $\mathbb{R}$ is the absolute value. The instance is `Real.normedAddCommGroup`, and the lemma `Real.norm_eq_abs` states $\|r\| = |r|$. It holds by definition, so `Real.norm_eq_abs` is a rewriting rule more than a theorem. The module `Mathlib.Analysis.Normed.Group.Real` adds the cases that `simp` uses: `Real.norm_of_nonneg` gives $\|r\| = r$ for $r \ge 0$, `Real.norm_of_nonpos` gives $\|r\| = -r$ for $r \le 0$, and `Real.norm_natCast` and `Real.norm_ofNat` compute the norm of a numeral. The lemma `Real.le_norm_self` states $r \le \|r\|$.

The integers and the rationals get the norm of $\mathbb{R}$ by restriction. The instances are `Int.instNormedAddCommGroup` and `Rat.instNormedAddCommGroup`. The lemmas `Int.norm_cast_real` and `Rat.norm_cast_real` state that the cast to $\mathbb{R}$ keeps the norm, and `Int.norm_eq_abs` states $\|n\| = |n|$ with the absolute value computed in $\mathbb{R}$. In each normed group the multiples satisfy $\|n \cdot a\| \le \|n\| \, \|a\|$ for $n \in \mathbb{Z}$, by `norm_zsmul_le`.

#### The circle

Let $p$ be a real number. The type `AddCircle p` is the quotient group $\mathbb{R}/p\mathbb{Z}$. The quotient norm of Chapter 4 gives it a norm, and the instance is `AddCircle.instNormedAddCommGroupReal`. The norm of the class of $x$ is the distance from $x$ to the nearest multiple of $p$. The lemma `AddCircle.norm_eq` computes it with the nearest integer:
$$\|[x]\| = \left| x - \operatorname{round}(x/p) \, p \right|.$$
*Proof sketch.* The quotient norm is $\inf_{k \in \mathbb{Z}} |x - kp|$. The function $k \mapsto |x - kp|$ takes its least value at the integer nearest to $x/p$. $\square$

So no class has norm larger than half the period: `AddCircle.norm_le_half_period` states $\|u\| \le |p|/2$ for $p \ne 0$. The bound is attained at $p/2$, by `AddCircle.norm_half_period_eq`. The norm of a point of the circle is its real representative exactly when this representative is short: `AddCircle.norm_coe_eq_abs_iff` states $\|[x]\| = |x|$ if and only if $|x| \le |p|/2$. For $p = 1$ the lemma `UnitAddCircle.norm_eq` gives $\|[x]\| = |x - \operatorname{round}(x)|$. The circle with $p = 2\pi$ is the domain of the Fourier series of Volume 19.

The points of finite order have rational norms. The lemma `AddCircle.norm_div_natCast` computes $\|[\tfrac{m}{n} p]\| = p \cdot \min(m \bmod n, \, n - m \bmod n)/n$, and `AddCircle.le_add_order_smul_norm_of_isOfFinAddOrder` states $p \le n \|u\|$ for a nonzero point $u$ of order $n$.

#### Subgroups and submodules

A subgroup of a normed group is a normed group with the restricted norm. The module `Mathlib.Analysis.Normed.Group.Subgroup` gives the instances `AddSubgroup.normedAddCommGroup` and `AddSubgroup.seminormedAddCommGroup`, and the forms `AddSubgroupClass.normedAddCommGroup` for any type of subobjects that are closed under the operations. The norm of an element of the subtype is the norm of its coercion, by definition. The module `Mathlib.Analysis.Normed.Group.Submodule` does the same for submodules, with `Submodule.normedAddCommGroup`, and for closed submodules, with `ClosedSubmodule.normedAddCommGroup`. The lemma `LinearMap.continuous_domRestrict` states that the restriction of a continuous linear map to a submodule is continuous.

#### The null subgroup and the separation quotient

Let $M$ be a seminormed group. The *null subgroup* is the set $N = \{x : \|x\| = 0\}$. It is a subgroup by the triangle inequality, and it is closed, because it is the preimage of $\{0\}$ under the continuous function $\|\cdot\|$. The module `Mathlib.Analysis.Normed.Group.NullSubmodule` defines it as `nullAddSubgroup M` and, for a seminormed space over $𝕜$, as the submodule `nullSubmodule 𝕜 E`. The membership lemma `mem_nullSubmodule_iff` states $x \in N \iff \|x\| = 0$, and `isClosed_nullSubmodule` states that $N$ is closed.

The null subgroup is the closure of $\{0\}$. So the quotient $M/N$ is the separation quotient `SeparationQuotient M` of the metric, and Section 4 shows that it is a normed group with $\|[x]\| = \|x\|$. The module `Mathlib.Analysis.Normed.Group.SeparationQuotient` gives the quotient map as a bounded group homomorphism, `SeparationQuotient.normedMk`, and the universal property for bounded homomorphisms.

| Lean name | Statement |
|---|---|
| `SeparationQuotient.norm_normedMk_le` | the quotient map has norm at most $1$ |
| `SeparationQuotient.norm_normedMk_eq_one` | it has norm $1$ when $M$ has a point of nonzero norm |
| `SeparationQuotient.liftNormedAddGroupHom` | a bounded homomorphism $f$ with $f(x) = 0$ for $\|x\| = 0$ factors through the quotient |
| `SeparationQuotient.norm_liftNormedAddGroupHom_le` | the factored map has norm at most $\|f\|$ |
| `SeparationQuotient.liftNormedAddGroupHomEquiv` | the factorization is a bijection between such maps $M \to N$ and maps $M/N \to N$ |

*Proof of the second line.* The quotient map keeps the norm, so its operator norm is at most $1$, and it is $1$ as soon as one point has nonzero norm. $\square$ The normed group homomorphisms of these statements are the objects of Chapter 2, Section 3.

#### Normed lattices

A lattice ordered group with a norm has a *solid* norm if $|x| \le |y|$ implies $\|x\| \le \|y\|$, where $|x| = x \vee (-x)$. The class `HasSolidNorm` of `Mathlib.Analysis.Normed.Order.Lattice` adds this axiom, and the field is `HasSolidNorm.solid`. The real numbers, the rationals, the integers and the functions $\iota \to \mathbb{R}$ with the sup norm have solid norms. A Banach lattice is a complete normed lattice of this kind.

The first consequence is $\|\,|a|\,\| = \|a\|$, by `norm_abs_eq_norm`, since $|a|$ and $a$ have the same absolute value. The second is the inequality `norm_abs_sub_abs`:
$$\|\,|a| - |b|\,\| \le \|a - b\|.$$
*Proof.* In a lattice ordered group, $\big|\,|a| - |b|\,\big| \le |a - b|$. Apply solidity. $\square$ The same argument gives `norm_sup_sub_sup_le_norm`, $\|x \vee z - y \vee z\| \le \|x - y\|$. So the lattice operations are Lipschitz with constant $1$: `lipschitzWith_sup_right`, `lipschitzWith_posPart` and `lipschitzWith_negPart`. The instance `HasSolidNorm.toTopologicalLattice` follows, and so does the closedness of the positive cone, `isClosed_nonneg`.

#### Order and distance in a product

The module `Mathlib.Analysis.Normed.Order.UpperLower` studies upper and lower sets in $\mathbb{R}$ and in $\mathbb{R}^\iota$ with the sup norm. The distance is monotone along the order: `dist_le_dist_of_le` states $d(a_1, b_1) \le d(a_2, b_2)$ when $a_2 \le a_1 \le b_1 \le b_2$. The lemma `dist_inf_sup` states $d(x \wedge y, x \vee y) = d(x, y)$. *Proof in $\mathbb{R}$.* The pair $\{x \wedge y, x \vee y\}$ is the pair $\{x, y\}$. $\square$ The thickening of an upper set is an upper set, by `IsUpperSet.thickening`, and `upperClosure_interior_subset` compares the upper closure of the interior with the interior of the upper closure. These lemmas serve to prove that order connected sets in $\mathbb{R}^n$ are measurable.

#### Moving a norm along a bijection

Let $e : \alpha \simeq \beta$ be a bijection of types and let $\beta$ be a normed group. The definition `Equiv.normedAddCommGroup e` puts on $\alpha$ the norm $\|a\| = \|e(a)\|$ and the group structure carried by $e$. The module `Mathlib.Analysis.Normed.Module.TransferInstance` also has `AddEquiv.normedSpace` for an additive equivalence, and the modules `Mathlib.Analysis.Normed.Ring.TransferInstance` and `Mathlib.Analysis.Normed.Field.TransferInstance` give `Equiv.normedRing` and `Equiv.normedField`. The module `Mathlib.Analysis.Normed.Module.Shrink` applies this to the type `Shrink α`, a copy of a small type in a lower universe, with `Shrink.instNormedAddCommGroup` and `Shrink.instNormedSpace`. These definitions are used to change universes in a proof.

#### Common errors

1. The norm on `AddCircle p` depends on $p$, not only on the group. The circles $\mathbb{R}/\mathbb{Z}$ and $\mathbb{R}/2\pi\mathbb{Z}$ are isomorphic groups with different norms.
2. `SeparationQuotient.norm_normedMk_eq_one` needs a point of nonzero norm. If all norms are $0$, the quotient is the trivial group and the quotient map has norm $0$.
3. `Equiv.normedAddCommGroup` is a definition, not an instance. A proof must install it with a local instance, and it is not compatible with an existing norm on $\alpha$.

### Exercises

1. (A) Compute $\|[7/3]\|$ in `AddCircle 1` with `UnitAddCircle.norm_eq`.
2. (A) Prove that the null subgroup of a seminormed group is a subgroup.
3. (B) Prove $\big|\,|a| - |b|\,\big| \le |a - b|$ in a lattice ordered group and derive `norm_abs_sub_abs`.
4. (B) Show that the norm on `AddCircle p` satisfies $\|n u\| \le |n| \|u\|$, and give $u$ and $n$ with strict inequality.
5. (B) Prove that a seminormed group is a normed group if and only if its null subgroup is trivial.
6. (C) Prove that a point $u \ne 0$ of order $n$ in $\mathbb{R}/p\mathbb{Z}$ has $\|u\| \ge p/n$.

### Reference

<?reference?>
