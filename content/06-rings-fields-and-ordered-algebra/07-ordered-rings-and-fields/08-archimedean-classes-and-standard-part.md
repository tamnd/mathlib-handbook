---
title: Archimedean classes, standard parts and maps into the reals
kind: api
modules:
  - Mathlib.Algebra.Order.Archimedean.Class
  - Mathlib.Algebra.Order.Archimedean.Hom
  - Mathlib.Algebra.Order.Archimedean.IndicatorCard
  - Mathlib.Algebra.Order.Archimedean.Real.Basic
  - Mathlib.Algebra.Order.Archimedean.Real.Hom
  - Mathlib.Algebra.Order.Archimedean.Submonoid
  - Mathlib.Algebra.Order.Ring.Archimedean
  - Mathlib.Algebra.Order.Ring.StandardPart
explains:
  E2: [ArchimedeanClass, ArchimedeanClass.mk, ArchimedeanClass.mk_le_mk, ArchimedeanClass.min_le_mk_add, ArchimedeanClass.mk_mul, ArchimedeanClass.addValuation, ArchimedeanClass.FiniteElement, ArchimedeanClass.stdPart, ArchimedeanClass.stdPart_mul, OrderRingHom.subsingleton]
  E1: auto
families: []
requires: [V06.C01, V06.C03, V04, V05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Archimedean classes, standard parts and maps into the reals

### Overview

Section 3 is about ordered fields in which every element is bounded by a natural number. This section is about the fields where this is false, and about what is left of the archimedean property in them. In a field of formal Laurent series or in a field of hyperreal numbers, there are infinitesimal elements, which are smaller than $1/n$ for all $n$, and infinite elements, which are larger than all $n$. Two elements are in the same archimedean class when each is bounded by a multiple of the other. The set of classes is a linear order, and in a ring the class of a product is the sum of the classes. So the class map is a valuation.

The section also gives the other side of the picture. An archimedean ordered field has exactly one order embedding into $\mathbb{R}$, and $\mathbb{R}$ has no ring maps to itself except the identity. In a field that is not archimedean, a finite element has a standard part: the unique real number that is infinitely close to it. The section needs the ordered rings and fields of Sections 1 and 2, the archimedean property of Section 3, the order theory of Volume 4 and the subgroups of Volume 5.

### The library around it

#### The archimedean class of an element

For a linearly ordered additive commutative group $M$, the type `ArchimedeanClass M` is the quotient of $M$ by the relation "each of $|a|, |b|$ is bounded by a natural multiple of the other". The class of $a$ is `ArchimedeanClass.mk a`. The order on the classes is the reverse of the order of the sizes: `ArchimedeanClass.mk_le_mk` says
$$\operatorname{mk} a \le \operatorname{mk} b \iff \exists n, \ |b| \le n \cdot |a|.$$
So a large element has a small class. The zero element is alone in its class, and its class is the top element: `ArchimedeanClass.mk_eq_top_iff` says $\operatorname{mk} a = \top \iff a = 0$. The strict form is `ArchimedeanClass.mk_lt_mk`: $\operatorname{mk} a < \operatorname{mk} b$ exactly when $n \cdot |b| < |a|$ for all $n$, that is, when $b$ is infinitely small compared with $a$.

The class does not see the sign: `ArchimedeanClass.mk_neg` and `ArchimedeanClass.mk_abs` say $\operatorname{mk}(-a) = \operatorname{mk} |a| = \operatorname{mk} a$. For a sum, `ArchimedeanClass.min_le_mk_add` says $\min(\operatorname{mk} a, \operatorname{mk} b) \le \operatorname{mk}(a + b)$. This is the ultrametric inequality of a valuation. When the classes are different, the smaller class wins: `ArchimedeanClass.mk_add_eq_mk_right` says that $\operatorname{mk} b < \operatorname{mk} a$ gives $\operatorname{mk}(a + b) = \operatorname{mk} b$. In words, adding an element that is infinitely smaller does not change the class.

If $M$ is archimedean, all nonzero elements are in one class, by `ArchimedeanClass.mk_eq_mk_of_archimedean`. So the type of classes has at most two elements: the class of the nonzero elements and $\top$. The number of classes measures how far $M$ is from being archimedean. The type `FiniteArchimedeanClass M` is the type of classes other than $\top$.

#### Subgroups from classes

An upper set $s$ of classes gives a subgroup `ArchimedeanClass.addSubgroup s`: the elements whose class is in $s$. It is closed under addition by `ArchimedeanClass.min_le_mk_add`, since an upper set contains everything above the minimum. The special cases `ArchimedeanClass.ballAddSubgroup c` and `ArchimedeanClass.closedBallAddSubgroup c` are the elements of class greater than $c$, and of class at least $c$. These subgroups are convex: an element between two elements of the subgroup is in it. A monotone group map $f : M \to N$ gives a monotone map of classes, `ArchimedeanClass.orderHom f`.

#### The class as a valuation

In a linearly ordered commutative ring $R$, the classes form an ordered additive monoid, and the class of a product is the sum: `ArchimedeanClass.mk_mul` says $\operatorname{mk}(x y) = \operatorname{mk} x + \operatorname{mk} y$. With `ArchimedeanClass.mk_one`, $\operatorname{mk} 1 = 0$, and with `ArchimedeanClass.min_le_mk_add`, this makes the class map an additive valuation, `ArchimedeanClass.addValuation R`, and `ArchimedeanClass.addValuation_apply` says that its value at $a$ is $\operatorname{mk} a$.

The sign of the class tells the size of the element. The class $0$ is the class of $1$, and of all nonzero natural numbers by `ArchimedeanClass.mk_natCast`. An element of positive class is infinitesimal, and an element of negative class is infinite. The lemma `ArchimedeanClass.exists_int_gt_of_mk_nonneg` says that an element of nonnegative class is bounded by an integer. In a field, `ArchimedeanClass.mk_ratCast` says that a nonzero rational number has class $0$. If $S$ is archimedean and $f : S \to R$ is a monotone additive map, `ArchimedeanClass.mk_map_of_archimedean` says that all nonzero images have the same class.

#### Finite elements and the standard part

For a linearly ordered field $K$, the elements of nonnegative class are the finite elements. They form the subring `ArchimedeanClass.FiniteElement K`, and `ArchimedeanClass.FiniteElement.mk` makes an element of it from $x$ and a proof of $0 \le \operatorname{mk} x$. It is a valuation ring, by `ArchimedeanClass.instValuationRingFiniteElement`: for two finite elements, one divides the other. A finite element is a unit exactly when it is not infinitesimal, by `ArchimedeanClass.FiniteElement.isUnit_iff_mk_eq_zero`. The quotient by the maximal ideal of infinitesimals is the residue field `ArchimedeanClass.FiniteResidueField K`, and `ArchimedeanClass.FiniteResidueField.mk` is the quotient map, as an ordered ring map.

The residue field is archimedean, so it embeds into $\mathbb{R}$. The composite is the standard part `ArchimedeanClass.stdPart : K → ℝ`. For a finite $x$, it is the unique real number $r$ with $x - r$ infinitesimal; for an infinite $x$ the value is $0$, by `ArchimedeanClass.stdPart_of_mk_ne_zero`. The lemma `ArchimedeanClass.stdPart_eq_sSup` gives a formula when an order embedding $f : \mathbb{R} \to K$ is given: $\operatorname{st}(x) = \sup \{ r \mid f(r) < x \}$. The lemma `ArchimedeanClass.stdPart_eq` is the form that is used to compute: if $f(s) \le x$ for $s < r$ and $x \le f(s)$ for $s > r$, then $\operatorname{st}(x) = r$. And `ArchimedeanClass.mk_sub_stdPart_pos` says that $x - f(\operatorname{st} x)$ is infinitesimal.

The standard part is additive and multiplicative on finite elements: `ArchimedeanClass.stdPart_add` and `ArchimedeanClass.stdPart_mul` need the hypotheses $0 \le \operatorname{mk} x$ and $0 \le \operatorname{mk} y$. The lemmas `ArchimedeanClass.stdPart_neg` and `ArchimedeanClass.stdPart_inv` have no hypotheses, because of the conventions. It fixes the integers, the rationals and the reals: `ArchimedeanClass.stdPart_intCast`, `ArchimedeanClass.stdPart_ratCast`, `ArchimedeanClass.stdPart_real` and `ArchimedeanClass.stdPart_map_real`.

#### Maps between archimedean fields

An order embedding into an archimedean field is unique. The instance `OrderRingHom.subsingleton` says that `α →+*o β` has at most one element when $\beta$ is an archimedean linearly ordered field. Proof idea: two such maps agree on $\mathbb{Q}$. If they differ at $x$, then a rational number lies between the two values, by the density of $\mathbb{Q}$ in $\beta$, and the order of $x$ and the rational number contradicts one of the maps. The instances `OrderRingIso.subsingleton_left` and `OrderRingIso.subsingleton_right` are the forms for isomorphisms, and `OrderRingHom.apply_eq_self` says that an order embedding of an archimedean field into itself is the identity.

The instance `Real.nonemptyOrderRingHom` gives the existence: every archimedean linearly ordered field has an order embedding into $\mathbb{R}$. With uniqueness, the archimedean ordered fields are exactly the ordered subfields of $\mathbb{R}$. For $\mathbb{R}$ itself the order condition is not needed. The lemma `ringHom_monotone` says that a ring map is monotone when every nonnegative element of the source is a square, because a ring map takes squares to squares. Every nonnegative real is a square, so every ring map $\mathbb{R} \to \mathbb{R}$ is monotone. So `Real.RingHom.unique` says that the identity is the only ring map, and `Real.ringHom_apply` gives $f(r) = r$.

#### Completeness of the reals and other results

The module `Mathlib.Algebra.Order.Archimedean.Real.Basic` gives the order structure of $\mathbb{R}$. The lemma `Real.exists_isLUB` gives the least upper bound property for a nonempty set that is bounded above, and `Real.cauSeq_converges` gives the convergence of Cauchy sequences. The supremum is total, with the conventions `Real.sSup_empty` and `Real.sSup_of_not_bddAbove`: both give $0$. The instance `Real.instFloorRing` gives $\mathbb{R}$ the floor function of Section 3.

The module `Mathlib.Algebra.Order.Archimedean.Submonoid` says that a submonoid of an archimedean monoid is archimedean, by `AddSubmonoidClass.instAddArchimedean` and `SubmonoidClass.instMulArchimedean`. The module `Mathlib.Algebra.Order.Archimedean.IndicatorCard` has one result, `Set.infinite_iff_tendsto_sum_indicator_atTop`: a set $s$ of natural numbers is infinite exactly when the sums $\sum_{k < n} r \cdot \mathbf{1}_s(k)$ tend to infinity, for a positive $r$ in an archimedean monoid.

#### Common errors

1. The order of the classes is the reverse of the order of the sizes. A large element has a small class, $\operatorname{mk} 0 = \top$, and an infinitesimal element has a positive class. Check the direction before using `ArchimedeanClass.mk_le_mk`.
2. `ArchimedeanClass.stdPart` is defined on all of $K$, with the value $0$ on infinite elements. So `ArchimedeanClass.stdPart_add` and `ArchimedeanClass.stdPart_mul` need finiteness hypotheses. For example, with an infinite $x$, $\operatorname{st}(x + (1 - x)) = 1$, but $\operatorname{st} x + \operatorname{st}(1 - x) = 0$.
3. `OrderRingHom.subsingleton` needs the target to be archimedean, not the source. There are many order embeddings of $\mathbb{R}$ into a field of hyperreal numbers.

### Exercises

1. (A) In $\mathbb{Z}$, find all the archimedean classes, and give $\operatorname{mk} 5$ and $\operatorname{mk} 0$.
2. (A) Use `ArchimedeanClass.mk_mul` to show that $\operatorname{mk}(x^2) = 2 \operatorname{mk} x$, and deduce that the square of an infinitesimal is infinitesimal.
3. (B) Prove `ArchimedeanClass.min_le_mk_add` from `ArchimedeanClass.mk_le_mk` and $|a + b| \le |a| + |b|$.
4. (B) Show that if $x$ is finite and not infinitesimal, then $x^{-1}$ is finite, and $\operatorname{st}(x^{-1}) = (\operatorname{st} x)^{-1}$.
5. (B) Prove that a ring map $f : \mathbb{R} \to \mathbb{R}$ is monotone, from the fact that every nonnegative real is a square.
6. (C) Let $t$ be a positive infinitesimal. Show that $\operatorname{st}(t^{-1} \cdot t) \neq \operatorname{st}(t^{-1}) \operatorname{st}(t)$, and then prove `ArchimedeanClass.stdPart_add` from `ArchimedeanClass.stdPart_eq`.

### Reference

<?reference?>
