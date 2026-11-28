---
title: Fundamental domains and the geometry of numbers
kind: api
modules:
  - Mathlib.MeasureTheory.Group.FundamentalDomain
  - Mathlib.MeasureTheory.Group.GeometryOfNumbers
  - Mathlib.MeasureTheory.Group.FoelnerFilter
explains:
  E2: [MeasureTheory.IsFundamentalDomain, MeasureTheory.IsFundamentalDomain.measure_eq, MeasureTheory.IsFundamentalDomain.lintegral_eq_tsum, MeasureTheory.IsFundamentalDomain.exists_ne_one_smul_eq, MeasureTheory.covolume, MeasureTheory.QuotientMeasureEqMeasurePreimage, MeasureTheory.exists_pair_mem_lattice_not_disjoint_vadd, MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure, IsFoelner, IsFoelner.amenable]
  E1: auto
families: []
requires: [V13, V18.C02, V18.C03, V18.C04, V18.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Fundamental domains and the geometry of numbers

### Overview

The interval $[0, 1)$ meets every orbit of the action of $\mathbb{Z}$ on $\mathbb{R}$ by translation in exactly one point. The square $[0, 1)^2$ does the same for $\mathbb{Z}^2$ acting on $\mathbb{R}^2$. A set of this kind is a *fundamental domain*. It reduces questions about the whole space to questions about one piece: the integral over $\mathbb{R}$ of a function is the sum of its integrals over the translates of the piece. Measure theory only needs this up to null sets, and Mathlib defines fundamental domains in this weak form.

Two theorems of the geometry of numbers follow. The lemma of Blichfeldt says that a set of measure larger than a fundamental domain contains two points that differ by an element of the group. The theorem of Minkowski says that a convex set that is symmetric about $0$ and has volume larger than $2^n$ times the volume of a fundamental domain of a lattice contains a lattice point other than $0$.

The section also explains Følner sequences. These are sets that are almost invariant under the action, and they give invariant means. The section needs the invariant measures of Section 1 of this chapter, the measures of Chapter 2, Haar measure from Chapter 3 and the integrals of Chapters 4 and 5.

### The library around it

#### The definition

The structure `MeasureTheory.IsFundamentalDomain G s μ` has three fields, for a group `G` that acts on a measure space:

1. `s` is null measurable;
2. almost every point $x$ has a translate $g \cdot x$ in `s`;
3. the translates $g \cdot s$ for distinct $g$ are pairwise almost disjoint.

The additive version `MeasureTheory.IsAddFundamentalDomain` is the one for lattices in $\mathbb{R}^n$. The measure is an `autoParam` with default `volume`.

There are three constructors. `MeasureTheory.IsFundamentalDomain.mk'` takes a null measurable set that meets every orbit in exactly one point. This is the usual way to prove that $[0, 1)$ is a fundamental domain. `MeasureTheory.IsFundamentalDomain.mk` takes the three fields. `MeasureTheory.IsFundamentalDomain.mk_of_measure_univ_le` works for a finite measure: it replaces the covering condition by $\mu(X) \le \sum_g \mu(g \cdot s)$.

New fundamental domains come from old ones. The translate of a fundamental domain by an element that commutes with the action is a fundamental domain, by `MeasureTheory.IsFundamentalDomain.smul_of_comm`. The lemmas `MeasureTheory.IsFundamentalDomain.image_of_equiv` and `MeasureTheory.IsFundamentalDomain.preimage_of_equiv` move a fundamental domain along an equivalence of spaces and groups. The translates of a fundamental domain cover the space up to a null set, by `MeasureTheory.IsFundamentalDomain.iUnion_smul_ae_eq`.

#### Measures and integrals over a fundamental domain

All results below assume that `G` is countable and that `μ` is invariant under the action. The main formula is the decomposition of the integral:
$$\int_X f \, d\mu = \sum_{g \in G} \int_{g \cdot s} f \, d\mu.$$
The lemma `MeasureTheory.IsFundamentalDomain.lintegral_eq_tsum` is this formula for the lower integral. The lemma `MeasureTheory.IsFundamentalDomain.integral_eq_tsum` is the version for the Bochner integral and an integrable function. The primed forms `MeasureTheory.IsFundamentalDomain.lintegral_eq_tsum'` and `MeasureTheory.IsFundamentalDomain.integral_eq_tsum'` move the translation onto the function: they integrate $f(g^{-1} \cdot x)$ over $s$. The lemmas `MeasureTheory.IsFundamentalDomain.lintegral_eq_tsum_of_ac` and `MeasureTheory.IsFundamentalDomain.integral_eq_tsum_of_ac` replace `μ` by a measure that is absolutely continuous with respect to it.

Two fundamental domains have the same measure, by `MeasureTheory.IsFundamentalDomain.measure_eq`. More generally, the integral of an invariant function over a fundamental domain does not depend on the domain, by `MeasureTheory.IsFundamentalDomain.setIntegral_eq` and `MeasureTheory.IsFundamentalDomain.setLIntegral_eq`. The essential supremum of an invariant function on a fundamental domain is its essential supremum on the whole space, by `MeasureTheory.IsFundamentalDomain.essSup_measure_restrict`. The lemma `MeasureTheory.IsFundamentalDomain.measure_eq_card_smul_of_smul_ae_eq_self` treats a finite group: an invariant set has $|G|$ times the measure of its part in the domain.

#### The lemma of Blichfeldt

The lemma `MeasureTheory.IsFundamentalDomain.measure_le_of_pairwise_disjoint` says that if the pieces $g \cdot t \cap s$ are pairwise almost disjoint, then $\mu(t) \le \mu(s)$. The proof cuts $t$ along the translates of $s$ and moves each piece into $s$. The contrapositive is the lemma of Blichfeldt: `MeasureTheory.IsFundamentalDomain.exists_ne_one_smul_eq` says that if $\mu(s) < \mu(t)$, then there are points $x, y \in t$ and $g \ne 1$ with $g \cdot x = y$. For a lattice $L$ acting on a vector space, `MeasureTheory.exists_pair_mem_lattice_not_disjoint_vadd` says that two distinct translates $x + t$ and $y + t$ with $x, y \in L$ meet.

#### The theorem of Minkowski

The file `Mathlib.MeasureTheory.Group.GeometryOfNumbers` proves the theorem of Minkowski. Let $E$ be a finite dimensional real vector space of dimension $n$ with a Haar measure, $L$ a countable subgroup with a fundamental domain $F$, and $s$ a convex set with $-s = s$. The lemma `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` says:
$$2^n \mu(F) < \mu(s) \implies s \text{ contains a point of } L \setminus \{0\}.$$
The proof applies the lemma of Blichfeldt to $\tfrac{1}{2} s$. This gives $x \ne y$ in $\tfrac{1}{2} s$ with $x - y \in L$. Symmetry and convexity put $x - y = \tfrac{1}{2}(2x) + \tfrac{1}{2}(-2y)$ in $s$. The lemma `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure` allows equality, for a compact set and a discrete lattice. Algebraic number theory uses these lemmas to prove the finiteness of the class group and the unit theorem of Dirichlet.

#### Interior, frontier and quotient measures

The set `MeasureTheory.fundamentalInterior G s` contains the points of `s` that are in no other translate $g \cdot s$, and `MeasureTheory.fundamentalFrontier G s` contains the rest of `s`. For a fundamental domain the frontier is null, by `MeasureTheory.IsFundamentalDomain.measure_fundamentalFrontier`, and the interior is a fundamental domain whose translates are disjoint, by `MeasureTheory.IsFundamentalDomain.fundamentalInterior` and `MeasureTheory.pairwise_disjoint_fundamentalInterior`.

A fundamental domain defines a measure on the space of orbits. The class `MeasureTheory.QuotientMeasureEqMeasurePreimage ν μ` says that a measure `μ` on the quotient is the image of `ν` restricted to any fundamental domain. The lemma `MeasureTheory.IsFundamentalDomain.quotientMeasureEqMeasurePreimage` gives the class for this image measure. Then `MeasureTheory.IsFundamentalDomain.measurePreserving_quotient_mk` says that the quotient map from the domain to the quotient is measure preserving.

The class `MeasureTheory.HasFundamentalDomain G α ν` says that a fundamental domain exists. Under this class, `MeasureTheory.covolume G α ν` is the measure of any fundamental domain, and `MeasureTheory.IsFundamentalDomain.covolume_eq_volume` computes it from one domain. The covolume of $\mathbb{Z}^n$ in $\mathbb{R}^n$ is $1$.

#### Følner sequences and amenability

The file `Mathlib.MeasureTheory.Group.FoelnerFilter` treats sets that are almost invariant. The structure `IsFoelner G μ l F` says that a family of sets $F_i$, indexed along a filter $l$, has three properties. Eventually, each $F_i$ is measurable with $0 < \mu(F_i) < \infty$. And for each $g$,
$$\frac{\mu(g \cdot F_i \,\triangle\, F_i)}{\mu(F_i)} \to 0.$$
The intervals $[-n, n]$ form a Følner sequence for the action of $\mathbb{R}$ on itself by translation. On a finite measure space the constant family equal to the whole space is Følner, by `IsFoelner.univ_of_isFiniteMeasure`.

The filter `maxFoelner G μ` on sets is the largest Følner filter, and `isFoelner_iff_tendsto` says that a family is Følner if and only if it tends to this filter. Along an ultrafilter, the densities $\mu(s \cap F_i) / \mu(F_i)$ converge, and `IsFoelner.mean` is their limit. This mean is finitely additive, by `IsFoelner.mean_union_eq_add_of_disjoint`. It is invariant, by `IsFoelner.mean_smul_eq_mean`. The lemma `IsFoelner.amenable` packages these facts: a Følner family gives a finitely additive invariant mean $m$ with $m(X) = 1$. The lemma `amenable_of_maxFoelner_neBot` states the same under the hypothesis that `maxFoelner G μ` is not the trivial filter.

#### Common errors

1. Using the multiplicative names for a lattice. Lattices act by addition, so the predicate is `MeasureTheory.IsAddFundamentalDomain`, and the integral formula is `MeasureTheory.IsAddFundamentalDomain.lintegral_eq_tsum`.
2. Forgetting that the group must be countable. The decomposition of the integral is a countable sum, and every lemma of this kind has a `Countable G` hypothesis.
3. Expecting `IsFoelner.mean` to be a measure. It is only finitely additive, and it depends on the choice of ultrafilter.

### Exercises

1. (A) Show that $[0, 1)$ is a fundamental domain for the action of $\mathbb{Z}$ on $\mathbb{R}$, with `MeasureTheory.IsAddFundamentalDomain.mk'`.
2. (A) Show that $[0, 1)$ and $[a, a + 1)$ have the same measure as fundamental domains, with `MeasureTheory.IsAddFundamentalDomain.measure_eq`.
3. (B) Show that every measurable set $t \subseteq \mathbb{R}$ of measure greater than $1$ contains two points whose difference is a nonzero integer.
4. (B) Show that every convex set in $\mathbb{R}^2$ with $-s = s$ and area greater than $4$ contains a point of $\mathbb{Z}^2$ other than $0$.
5. (B) Show that the intervals $[-n, n]$ form a Følner sequence for the action of $\mathbb{Z}$ on $\mathbb{R}$ by translation.
6. (C) Prove that $\int_{\mathbb{R}} f = \int_0^1 \sum_{n \in \mathbb{Z}} f(x + n) \, dx$ for every integrable $f$.

### Reference

<?reference?>
