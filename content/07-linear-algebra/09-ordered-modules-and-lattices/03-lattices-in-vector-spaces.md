---
title: Lattices in vector spaces
kind: api
modules:
  - Mathlib.Algebra.Module.Lattice
  - Mathlib.Algebra.Module.Lattice.Basic
  - Mathlib.Algebra.Module.Lattice.Full
  - Mathlib.Algebra.Module.ZLattice.Basic
  - Mathlib.Algebra.Module.ZLattice.Covolume
  - Mathlib.Algebra.Module.ZLattice.Summable
explains:
  E2: [Submodule.IsLattice, Submodule.IsLattice.iff_fg_and_finrank_span_eq_finrank, Submodule.IsFullLattice, Module.Basis.extendOfIsFullLattice, IsZLattice, ZLattice.rank, ZSpan.fundamentalDomain, ZSpan.fract, ZLattice.covolume, ZLattice.summable_norm_rpow]
  E1: auto
families: []
requires: [V05, V06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Lattices in vector spaces

### Overview

A lattice in $\mathbb{R}^n$ is a subgroup such as $\mathbb{Z}^n$: it is discrete, and it spans the space. Lattices are the main objects of the geometry of numbers. The ring of integers of a number field is a lattice in its Minkowski space, and the periods of an elliptic curve form a lattice in $\mathbb{C}$. Mathlib has two notions. The algebraic notion is a finitely generated $R$-submodule of an $A$-module whose independent sets over $R$ stay independent over $A$, for example a $\mathbb{Z}$-submodule of a $\mathbb{Q}$-vector space. The analytic notion is a discrete $\mathbb{Z}$-submodule of a normed space that spans it. This section covers both notions, the fundamental domain of a basis, the covolume, and the convergence of the series $\sum_{z \in L} \|z\|^r$. In this sense a lattice is a module, and it is not related to the lattices of order theory.

### The library around it

#### Algebraic lattices

Let $R$ be a commutative ring, $A$ an $R$-algebra, and $V$ an $A$-module. The class `Submodule.IsLattice A M` says that the $R$-submodule $M$ of $V$ is finitely generated and that each $R$-linearly independent subset of $M$ is $A$-linearly independent (`Submodule.isLattice_iff`). A lattice need not span $V$. For example, $\mathbb{Z} \cdot (1, 0)$ is a lattice in $\mathbb{Q}^2$, and $\mathbb{Z} + \mathbb{Z}\sqrt{2}$ is not a lattice in $\mathbb{R}$, since $1$ and $\sqrt{2}$ are independent over $\mathbb{Z}$ and dependent over $\mathbb{R}$.

**Theorem.** Let $K$ be a field with an injective map $R \to K$, and let $M$ be an $R$-submodule of a $K$-vector space. Then $M$ is a lattice if and only if $M$ is finitely generated and the dimension of its $K$-span is the rank of $M$ over $R$.

*Proof.* Suppose that $M$ is a lattice. A maximal $R$-independent subset $s$ of $M$ has $\operatorname{rank}_R M$ elements, and it is $K$-independent. Each element of $M$ is $K$-dependent on $s$, since some nonzero multiple of it over $R$ is in the $R$-span of $s$. So $s$ is a $K$-basis of the span. Conversely, let $t \subseteq M$ be $R$-independent and suppose that $t$ is $K$-dependent. Extend $t$ to a maximal $R$-independent set of $\operatorname{rank}_R M$ elements. It spans the $K$-span of $M$ and is $K$-dependent, so the span has a dimension less than $\operatorname{rank}_R M$, which is false. $\square$

This is `Submodule.IsLattice.iff_fg_and_finrank_span_eq_finrank`. Over the fraction field of $R$, each finitely generated submodule is a lattice (`Submodule.IsLattice.iff_fg`), since the denominators can be cleared. Over a principal ideal domain, a lattice is a free module (`Submodule.IsLattice.free`). The class is kept by submodules that are finitely generated (`Submodule.IsLattice.mono_of_fg`) and by scalar multiples, and over a field the sum of two lattices is a lattice (`Submodule.IsLattice.sup`). The $R$-span of a $K$-independent family is a lattice (`Submodule.IsLattice.span_of_linearIndependent`).

#### Full lattices

A lattice is full if its $A$-span is all of $V$: `Submodule.IsFullLattice A M`, with `Submodule.IsFullLattice.span_eq_top`. Then $V$ is finite-dimensional over $K$, and the rank of $M$ over $R$ is the dimension of $V$ (`Submodule.IsFullLattice.finrank_eq`). Conversely, a lattice whose rank is at least the dimension of $V$ is full (`Submodule.IsFullLattice.of_finrank_le`).

An $R$-basis of a full lattice is a $K$-basis of $V$. This is the definition `Module.Basis.extendOfIsFullLattice`. A larger finitely generated submodule of a full lattice is a full lattice (`Submodule.IsFullLattice.of_le_of_fg`). Over the fraction field of a Noetherian domain, the intersection of two full lattices is a full lattice, by the instance `Submodule.IsFullLattice.inf`. For $V = K^n$ the rank of a full lattice is therefore $n$.

#### Discrete lattices

Now let $E$ be a finite-dimensional real normed space, or more generally a normed space over a normed field $K$ with a floor function. The class `IsZLattice K L` says that a $\mathbb{Z}$-submodule $L$ of $E$ with `DiscreteTopology L` spans $E$ over $K$ (`IsZLattice.span_top`). The main source of examples is the $\mathbb{Z}$-span of a basis of $E$, which is a discrete lattice by the instance `instIsZLatticeRealSpan`. The results on the span of a basis have names that start with ZSpan, and the results on a discrete lattice have names that start with ZLattice.

For a basis $b$ of $E$, the fundamental domain `ZSpan.fundamentalDomain b` is the set of the vectors whose coordinates are all in $[0, 1)$ (`ZSpan.mem_fundamentalDomain`). The floor `ZSpan.floor b x` is the lattice vector with the integer parts of the coordinates of $x$, and the fractional part `ZSpan.fract b x` is $x$ minus the floor. Two vectors have the same fractional part if and only if they differ by a lattice vector (`ZSpan.fract_eq_fract`). So each vector has exactly one translate in the fundamental domain (`ZSpan.exist_unique_vadd_mem_fundamentalDomain`), and the quotient $E / L$ is in bijection with the fundamental domain (`ZSpan.quotientEquiv`). The domain is bounded and measurable, and it is a fundamental domain for the action of $L$ in the sense of measure theory (`ZSpan.isAddFundamentalDomain`).

A bounded set meets the span of a basis in a finite set (`ZSpan.setFinite_inter`). This fact gives the structure of a discrete lattice.

**Theorem.** Let $L$ be a discrete lattice in a real vector space $E$ of dimension $n$. Then $L$ is a free $\mathbb{Z}$-module of rank $n$.

*Proof.* Since $L$ spans $E$, it contains a basis $b$ of $E$. Let $L_0$ be the $\mathbb{Z}$-span of $b$, and $F$ its fundamental domain. Each $x \in L$ is $\operatorname{floor}(x) + \operatorname{fract}(x)$, with the floor in $L_0$ and the fractional part in $L \cap \bar F$. The set $L \cap \bar F$ is discrete and bounded, so it is finite. Thus $L$ is generated by $b$ and a finite set, so it is finitely generated. It is torsion free, so it is free. Since $L_0 \le L$ and $L / L_0$ is finite, the rank of $L$ is the rank of $L_0$, which is $n$. $\square$

These are `ZLattice.FG`, `ZLattice.module_free` and `ZLattice.rank`. A $\mathbb{Z}$-basis of $L$ gives a basis of $E$ by `Module.Basis.ofZLatticeBasis`, whose $\mathbb{Z}$-span is $L$ (`Module.Basis.ofZLatticeBasis_span`). For $L \le \mathbb{R}^n$, the choice `IsZLattice.basis L` gives a basis directly. The pullback of a lattice along a linear equivalence is `ZLattice.comap`, and `ZLattice.comap_equiv` identifies the two lattices.

#### The covolume

For a discrete lattice $L$ in a real space $E$ with a Haar measure $\mu$, `ZLattice.covolume L μ` is the measure of a fundamental domain of $L$. Each fundamental domain gives the same value (`ZLattice.covolume_eq_measure_fundamentalDomain`), and the value is positive (`ZLattice.covolume_pos`).

**Theorem.** Let $L \le \mathbb{R}^n$ be a discrete lattice with a $\mathbb{Z}$-basis $b_1, \ldots, b_n$. Then the covolume of $L$ for the Lebesgue measure is $|\det(b_1, \ldots, b_n)|$.

*Proof.* The fundamental domain of $b$ is the image of the unit cube $[0, 1)^n$ under the linear map that sends $e_i$ to $b_i$. A linear map multiplies the Lebesgue measure by the absolute value of its determinant, and the unit cube has measure $1$. $\square$

This is `ZLattice.covolume_eq_det`, and `ZSpan.volume_fundamentalDomain` is the same computation for the span of a basis. For a sublattice $L_1 \le L_2$, the ratio of the covolumes is the index: $\operatorname{covol}(L_1) / \operatorname{covol}(L_2) = [L_2 : L_1]$ (`ZLattice.covolume_div_covolume_eq_relIndex`), since a fundamental domain of $L_1$ is the union of $[L_2 : L_1]$ translates of a fundamental domain of $L_2$. The covolume also counts lattice points: for a bounded measurable set $s$ whose boundary has measure $0$, the number of points of $\frac{1}{n} L$ in $s$, divided by $n^d$, tends to $\mu(s) / \operatorname{covol}(L)$ (`ZLattice.covolume.tendsto_card_div_pow`).

#### Sums over a lattice

The file `Mathlib.Algebra.Module.ZLattice.Summable` proves that $\sum_{z \in L} \|z\|^r$ converges when $r < -d$, where $d$ is the rank of $L$. This is `ZLattice.summable_norm_rpow`, with `ZLattice.summable_norm_sub_rpow` for the shifted sum $\sum_{z} \|z - x\|^r$ and the explicit bound `ZLattice.tsum_norm_rpow_le`. The proof compares the norm with the largest coordinate in a $\mathbb{Z}$-basis: there is $c > 0$ with $c |x_i| \le \|x\|$ for each coordinate $x_i$ (`ZLattice.normBound_spec`). The lattice points with largest coordinate $k$ are at most $2d (2k + 1)^{d - 1}$ in number, so the sum is bounded by a constant times $\sum_k k^{d - 1 + r}$, which converges for $r < -d$. These sums are the Eisenstein series of a lattice in $\mathbb{C}$, where $d = 2$.

The module Mathlib.Algebra.Module.Lattice has no declarations of its own.

#### Common errors

1. Confusing `Submodule.IsLattice` with `IsZLattice`. The first is algebraic and does not require the lattice to span; the second needs `DiscreteTopology L` and requires the span to be the whole space.
2. Using `ZSpan.fundamentalDomain` of a lattice without a basis. It takes a basis of $E$; for a discrete lattice, first take `Module.Basis.ofZLatticeBasis` of a $\mathbb{Z}$-basis of $L$.
3. Forgetting the measure in `ZLattice.covolume`. It takes a measure argument with the volume as the default; the determinant formula `ZLattice.covolume_eq_det` is for the volume on $\mathbb{R}^n$ only.

### Exercises

1. (A) Show that $\mathbb{Z} + \mathbb{Z} \sqrt{2}$ is not discrete in $\mathbb{R}$, and is a full lattice in the $\mathbb{Q}$-vector space $\mathbb{Q}(\sqrt{2})$.
2. (A) Compute the covolume of the lattice in $\mathbb{R}^2$ spanned by $(2, 1)$ and $(1, 3)$.
3. (B) Show that the index of $2 \mathbb{Z}^n$ in $\mathbb{Z}^n$ is $2^n$, with `ZLattice.covolume_div_covolume_eq_relIndex`.
4. (B) Find a finitely generated $\mathbb{Z}$-submodule of $\mathbb{R}^2$ that spans $\mathbb{R}^2$ and is not discrete.
5. (B) Show that the intersection of two full lattices in $\mathbb{Q}^n$ is a full lattice, with an explicit example in $\mathbb{Q}^2$.
6. (C) Show that $\sum_{z \in \mathbb{Z}^2 \setminus 0} \|z\|^{-2}$ diverges, so the bound $r < -d$ in `ZLattice.summable_norm_rpow` is sharp.

### Reference

<?reference?>
