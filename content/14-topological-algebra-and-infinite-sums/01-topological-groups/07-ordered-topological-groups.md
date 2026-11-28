---
title: Ordered topological groups
kind: api
modules:
  - Mathlib.Topology.Algebra.Group.Order
  - Mathlib.Topology.Algebra.Order.Group
  - Mathlib.Topology.Algebra.Order.Archimedean
  - Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete
  - Mathlib.Topology.Algebra.Order.UpperLower
  - Mathlib.Topology.Algebra.Order.Support
  - Mathlib.Topology.Algebra.Order.Module
  - Mathlib.Topology.Instances.Sign
explains:
  E2: [LinearOrderedAddCommGroup.toIsTopologicalAddGroup, tendsto_zero_iff_abs_tendsto_zero, Filter.map_add_left_nhdsGT, AddSubgroup.dense_of_not_isolated_zero, AddSubgroup.dense_or_isCyclic, AddSubgroup.isAddCyclic_iff_discreteTopology, HasUpperLowerClosure, IsPreconnected.sign_eq_of_continuousOn]
  E1: auto
families: []
requires: [V05, V13.C01, V13.C04, V13.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Ordered topological groups

### Overview

The real line is a group, a linear order and a topological space, and the three structures fit together. This section collects the parts of the library that use an order and a topology on a group at the same time. The order topology on a linearly ordered group makes it a topological group. The absolute value is continuous, and a limit at zero is a limit of absolute values. Translations and negation move one sided neighbourhoods in the expected way.

The section also treats the subgroups of an archimedean group, which are either dense or cyclic, the closure of upper and lower sets, the sign function, and a few small facts about supports and nonnegative scalars.

### The library around it

#### The order topology makes a topological group

Let $G$ be a linearly ordered additive commutative group with the order topology, that is, with `IsOrderedAddMonoid G` and `OrderTopology G`. The instance `LinearOrderedAddCommGroup.toIsTopologicalAddGroup` says that addition and negation are continuous. The multiplicative form is `LinearOrderedCommGroup.toIsTopologicalGroup`. So the results of the earlier sections of this chapter apply to $\mathbb{Z}$, $\mathbb{Q}$, $\mathbb{R}$ and to each ordered group with its order topology.

The proof uses the basis of open intervals. For the sum $a + b$ and a neighbourhood $(a + b - \varepsilon, a + b + \varepsilon)$, the sum of the intervals around $a$ and $b$ of half the length lies inside it.

#### Absolute values and limits

| Lean name | Statement |
|---|---|
| `continuous_abs` | $x \mapsto \lvert x \rvert$ is continuous |
| `Continuous.abs` | if $f$ is continuous, so is $x \mapsto \lvert f(x) \rvert$ |
| `Filter.Tendsto.abs` | if $f \to a$, then $\lvert f \rvert \to \lvert a \rvert$ |
| `tendsto_zero_iff_abs_tendsto_zero` | $f \to 0$ if and only if $\lvert f \rvert \to 0$ |
| `comap_abs_nhds_zero` | the preimage of $\mathcal{N}(0)$ under $\lvert \cdot \rvert$ is $\mathcal{N}(0)$ |
| `tendsto_abs_nhdsNE_zero` | $\lvert \cdot \rvert$ sends the punctured neighbourhoods of $0$ to the right neighbourhoods of $0$ |
| `ContinuousAt.abs` | the pointwise form of `Continuous.abs` |
| `continuous_mabs` | the multiplicative form, for $\lvert x \rvert_m = \max(x, x^{-1})$ |

The lemma `comap_abs_nhds_zero` is the filter form of a simple fact: the sets $\{x \mid \lvert x \rvert < \varepsilon\}$ form a basis of neighbourhoods of $0$. The lemma `tendsto_zero_iff_abs_tendsto_zero` follows from it at once.

#### One sided neighbourhoods

The module `Mathlib.Topology.Algebra.Group.Order` moves the one sided neighbourhoods `nhdsWithin a (Set.Ioi a)` and `nhdsWithin a (Set.Iio a)` along the group operations. The names use the short forms *nhdsGT* for $(a, \infty)$, *nhdsLT* for $(-\infty, a)$, *nhdsGE* and *nhdsLE*. The group only needs a partial order, `IsOrderedAddMonoid` and the continuity of the operation that moves the filter.

1. Translation keeps the side: `Filter.map_add_left_nhdsGT` says that $x \mapsto c + x$ maps the right neighbourhoods of $a$ onto the right neighbourhoods of $c + a$. The lemmas `Filter.map_add_right_nhdsGT`, `Filter.map_add_left_nhdsLT` and `Filter.map_subRight_nhdsGT` are the other cases.
2. Negation changes the side: `Filter.neg_nhdsGT` says that $-\mathcal{N}_{>}(a) = \mathcal{N}_{<}(-a)$, and `tendsto_neg_nhdsGT` is the form with `Filter.Tendsto`. The lemma `Filter.map_subLeft_nhdsGT` is the same for $x \mapsto c - x$.
3. The forms `tendsto_neg_nhdsGT_neg` and `tendsto_neg_nhdsLE_neg` go from the neighbourhoods of $-a$ back to those of $a$.

The multiplicative forms, such as `Filter.inv_nhdsGT` and `Filter.map_mul_left_nhdsGT`, are for ordered multiplicative groups such as the positive reals. These lemmas often reduce a limit from the left to a limit from the right: compose with negation and use the lemma for the other side.

#### Subgroups of archimedean groups

Let $G$ be an archimedean linearly ordered group with the order topology, such as $\mathbb{R}$. A subgroup $S$ of $G$ is then either dense or cyclic. The library gives the result in several forms.

| Lean name | Statement |
|---|---|
| `AddSubgroup.dense_of_not_isolated_zero` | if $S$ has elements in each interval $(0, \varepsilon)$, then $S$ is dense |
| `AddSubgroup.dense_of_no_min` | if $S \ne 0$ and $S$ has no least positive element, then $S$ is dense |
| `AddSubgroup.dense_or_isCyclic` | each subgroup is dense or cyclic |
| `AddSubgroup.dense_xor_isAddCyclic` | in a densely ordered nontrivial group, exactly one of the two holds |
| `AddSubgroup.isAddCyclic_iff_discreteTopology` | a subgroup is cyclic if and only if its subspace topology is discrete |
| `AddSubgroup.instDiscreteTopologyZMultiples` | the subgroup $\mathbb{Z} g$ is discrete |
| `Rat.denseRange_cast` | $\mathbb{Q}$ is dense in an archimedean ordered field |

The proof of `AddSubgroup.dense_of_not_isolated_zero` is the classical one. Let $x < y$ in $G$, and take $g \in S$ with $0 < g < y - x$. By the archimedean property there is a least integer $n$ with $n g > x$. Then $n g = (n - 1) g + g \le x + g < y$, so $n g \in (x, y)$. If $S$ is not dense, then $S$ has a least positive element $g$, and the same argument shows that $S = \mathbb{Z} g$.

The lemma `denseRange_zsmul_iff_surjective` is a special case: the multiples of one element are dense only if they are all of $G$. In a densely ordered nontrivial group, `not_denseRange_zsmul` says that they are never dense. The multiplicative forms, such as `Subgroup.dense_of_not_isolated_one` and `Subgroup.dense_or_isCyclic`, need `MulArchimedean`.

#### Upper sets, lower sets and their closures

The class `HasUpperLowerClosure α` collects four facts about a preordered topological space: the closure of an upper set is an upper set, the closure of a lower set is a lower set, and the upper closure and the lower closure of an open set are open. The constructor `HasUpperLowerClosure.mk` takes the four facts. The instance `IsOrderedAddMonoid.to_hasUpperLowerClosure` says that an ordered additive commutative group with continuous translations has the property. The proof of the third fact is one line: the upper closure of $s$ is the union $\bigcup_{c \ge 0} (c + s)$ of translates of $s$, and each translate is open.

The consequences are `IsUpperSet.closure`, `IsLowerSet.closure`, `IsOpen.upperClosure`, `IsOpen.lowerClosure`, `IsUpperSet.interior`, `IsLowerSet.interior` and `Set.OrdConnected.interior`. The class goes to the order dual by `instHasUpperLowerClosureOrderDual`.

#### The sign function

The type `SignType` has three elements $-1$, $0$ and $1$, and it gets the discrete topology (`instTopologicalSpaceSignType` and `instDiscreteTopologySignType`). The function `SignType.sign` is continuous at each nonzero point of a linear order with the order topology: this is `continuousAt_sign_of_ne_zero`, with the forms `continuousAt_sign_of_pos` and `continuousAt_sign_of_neg`. The main consequence is `IsPreconnected.sign_eq_of_continuousOn`. If $f$ is continuous and has no zero on a preconnected set $s$, then $f$ has the same sign at all points of $s$. This is the intermediate value theorem in a short form.

#### Supports and nonnegative scalars

The module `Mathlib.Topology.Algebra.Order.Support` proves that the pointwise maximum and minimum of two functions with compact support have compact support: `HasCompactSupport.sup` and `HasCompactSupport.inf`, with the multiplicative forms `HasCompactMulSupport.sup` and `HasCompactMulSupport.inf`. The module `Mathlib.Topology.Algebra.Order.Module` restricts a continuous scalar action to the nonnegative scalars: `instContinuousSMulNonneg` and `instContinuousConstSMulNonneg` give the instances for the subtype `Nonneg R`, written $\{r \mid 0 \le r\}$.

#### Common errors

1. The names of the lemmas for one sided neighbourhoods use *nhdsGT* and *nhdsLT*, but the statements use `nhdsWithin a (Set.Ioi a)` and `nhdsWithin a (Set.Iio a)`. A search by the words of the statement does not find these names.
2. `AddSubgroup.dense_or_isCyclic` needs `Archimedean G`. The group $\mathbb{Z} \times \mathbb{Z}$ with the lexicographic order is not archimedean, and its subgroups do not satisfy the result.
3. `continuousAt_sign_of_ne_zero` fails at $0$. A proof that uses the continuity of the sign function must first show that the function has no zero.

### Exercises

1. (A) Use `tendsto_zero_iff_abs_tendsto_zero` to prove that $x_n \to 0$ in $\mathbb{R}$ if and only if $\lvert x_n \rvert \to 0$.
2. (A) Prove that the subgroup $\mathbb{Z} + \mathbb{Z}\sqrt{2}$ of $\mathbb{R}$ is dense with `AddSubgroup.dense_or_isCyclic`.
3. (B) Use `Filter.neg_nhdsGT` to deduce a limit from the left of $f(x)$ at $a$ from a limit from the right of $f(-x)$ at $-a$.
4. (B) Prove with `IsPreconnected.sign_eq_of_continuousOn` that a continuous function $f : [0, 1] \to \mathbb{R}$ with $f(0) < 0 < f(1)$ has a zero.
5. (C) Show that the upper closure of an open set in $\mathbb{R}^2$ with the product order is open, and give a closed set whose upper closure is not closed.

### Reference

<?reference?>
