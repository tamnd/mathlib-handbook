---
title: Notation classes, pointwise operations, support and indicator
kind: api
modules:
  - Mathlib.Algebra.Notation
  - Mathlib.Algebra.Notation.Bracket
  - Mathlib.Algebra.Notation.Defs
  - Mathlib.Algebra.Notation.FiniteSupport
  - Mathlib.Algebra.Notation.Indicator
  - Mathlib.Algebra.Notation.Lemmas
  - Mathlib.Algebra.Notation.Pi.Basic
  - Mathlib.Algebra.Notation.Pi.Defs
  - Mathlib.Algebra.Notation.Prod
  - Mathlib.Algebra.Notation.Support
  - Mathlib.Algebra.Group.Support
  - Mathlib.Algebra.Group.Indicator
explains:
  E2: [Set.indicator, Set.indicator_indicator, Set.support_indicator, Set.indicator_eq_self, Function.support, Function.support_binop_subset, Pi.single, Pi.single_apply, Pi.support_single]
  E1: auto
families: []
requires: [V01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Notation classes, pointwise operations, support and indicator

### Overview

Before Mathlib states a single group axiom, it fixes the symbols. A class such as the class of the symbol $+_v$ has one field and no laws. It only lets Lean read the symbol. The modules of this section hold these notation classes, and the first lemmas that need nothing but the symbols: the lemmas that move an operation into an `if then else`, the operations on functions and on pairs, the support of a function, the functions that are zero except at one point, and the indicator function of a set.

All these modules come before the class `Monoid`. So their lemmas hold with no algebraic laws at all. A lemma such as `Pi.mul_apply` needs only a multiplication on each factor, and the lemma `Set.indicator_indicator` needs only a zero. Section 1 of this chapter builds the classes with laws on top of these symbols. Later volumes use the support and the indicator in sums, in finitely supported functions and in the integral.

### The library around it

#### The notation classes

The module `Mathlib.Algebra.Notation.Defs` defines the classes for the symbols that the core of Lean does not give. Each class has one field.

| Lean name | Symbol and use |
|---|---|
| `VAdd` | $g +_v p$, an additive action of $G$ on $P$ |
| `HVAdd` | the heterogeneous form of $+_v$, with a third type for the result |
| `VSub` | $p -_v q$, the difference of two points, a value in $G$ |
| `SDiv` | the multiplicative form of $-_v$ |
| `Star` | the star operation $x \mapsto x^*$, with no default symbol |

The fields are `VAdd.vadd`, `HVAdd.hVAdd`, `VSub.vsub`, `SDiv.sdiv` and `Star.star`. The symbols $+_v$ and $-_v$ serve the torsors of Chapter 6: a group acts on a set of points, and two points have a difference in the group. The lemmas `VAdd.ext` and `VSub.ext` say that two instances with the same operation are equal. The attribute `to_additive` links each multiplicative class to its additive class, so one proof gives two lemmas.

The module `Mathlib.Algebra.Notation` gives the classes `PosPart`, `NegPart`, `OneLePart` and `LeOnePart`. They carry the positive part $a^+$ and the negative part $a^-$ of an element of an ordered group, and their multiplicative forms. The fields are `PosPart.posPart`, `NegPart.negPart`, `OneLePart.oneLePart` and `LeOnePart.leOnePart`. Volume 4 gives the laws: for an element $a$ of a lattice ordered group, $a^+ = a \vee 0$ and $a = a^+ - a^-$.

The module `Mathlib.Algebra.Notation.Bracket` gives the class `Bracket` with the field `Bracket.bracket`. It is the symbol of a bracket $[x, y]$ with $x$ in $L$ and $y$ and the result in $M$. The commutator $[a, b] = a b a^{-1} b^{-1}$ of two elements of a group, the commutator of two subgroups and the Lie bracket all use this one symbol.

The same module states two instances that are easy to miss: `Zero.instNonempty` and `One.instNonempty`. A type with a zero or with a one is not empty, because it has that element.

#### Operations and the conditional

The lemmas of `Mathlib.Algebra.Notation.Defs` move a binary operation into a conditional. The names follow a fixed pattern. The name puts the operation and the conditional in the order of the left side of the statement.

| Lean name | Statement |
|---|---|
| `mul_ite` | $a \cdot (\text{if } P \text{ then } b \text{ else } c) = \text{if } P \text{ then } a b \text{ else } a c$ |
| `ite_mul` | $(\text{if } P \text{ then } a \text{ else } b) \cdot c = \text{if } P \text{ then } a c \text{ else } b c$ |
| `ite_mul_ite` | the product of two conditionals on the same $P$ is one conditional |
| `mul_dite` | the form of `mul_ite` for a dependent conditional |
| `div_ite`, `ite_div` | the same for division |
| `add_ite`, `ite_sub` | the same for the additive operations |
| `neg_ite` | $-(\text{if } P \text{ then } b \text{ else } c) = \text{if } P \text{ then } -b \text{ else } -c$ |

Each proof is a case split on $P$, and in each case both sides are equal by definition. These lemmas are not simp lemmas. The tactic `split_ifs` often does the same work. They are useful when a rewrite must keep the conditional.

The module `Mathlib.Algebra.Notation.Lemmas` gives the order forms: `one_le_ite` and `ite_le_one` say that a conditional of two elements at least $1$ is at least $1$, and `ite_nonneg` and `ite_pos` are the additive forms. The dependent forms are `one_le_dite` and `dite_nonneg`. They need only an order and a one, not an ordered monoid.

#### Operations on functions and on pairs

Let $M_i$ be a family of types, one for each $i$ in $I$. If each $M_i$ has a multiplication, then the functions $f$ with $f(i) \in M_i$ have the pointwise multiplication $(f g)(i) = f(i) g(i)$. The module `Mathlib.Algebra.Notation.Pi.Defs` gives this instance `Pi.instMul`, and the same for the other symbols: `Pi.instOne`, `Pi.instInv`, `Pi.instDiv`, `Pi.instPow`, `Pi.instSMul`, `Pi.instVAdd` and `Pi.instStarForall`, with the additive forms.

Each instance has three lemmas. The lemma `Pi.mul_apply` is the simp lemma $(f g)(i) = f(i) g(i)$. The lemma `Pi.mul_def` states $f g = (i \mapsto f(i) g(i))$ as an equation of functions. The lemma `Pi.mul_comp` composes on the right. The names `Pi.one_apply`, `Pi.pow_apply`, `Pi.smul_apply`, `Pi.zero_apply` and `Pi.one_def` follow the same pattern. The constant functions have their own lemmas, such as `Function.const_mul`, `Function.const_one` and `Function.smul_const`.

The module `Mathlib.Algebra.Notation.Prod` does the same for a product $M \times N$. The instances are `Prod.instMul`, `Prod.instOne`, `Prod.instInv`, `Prod.instPow`, `Prod.instSMul`, `Prod.instStar` and their additive forms. The lemmas come in three shapes.

1. Projections, such as `Prod.fst_mul`: $(p q)_1 = p_1 q_1$, and `Prod.fst_one`.
2. Pairs, such as `Prod.mk_mul_mk`: $(a_1, b_1)(a_2, b_2) = (a_1 a_2, b_1 b_2)$, and `Prod.pow_mk` and `Prod.smul_mk`.
3. The swap, such as `Prod.swap_mul`: the swap of a product is the product of the swaps.

The lemma `Prod.mk_eq_one` says that $(x, y) = 1$ if and only if $x = 1$ and $y = 1$. All these proofs are by definition. The group structure on a product, and its universal property, are in the next chapter.

#### The function at one point

Let $I$ have a decidable equality and let each $M_i$ have a zero. For $i \in I$ and $x \in M_i$, the function `Pi.single i x` takes the value $x$ at $i$ and $0$ at each other point. It is in `Mathlib.Algebra.Notation.Pi.Basic`. For a constant family, `Pi.single_apply` gives the value at $i'$: it is $x$ if $i' = i$ and $0$ otherwise. In a vector space $K^n$, the function `Pi.single i 1` is the $i$-th standard basis vector. The multiplicative form `Pi.mulSingle` takes the value $1$ off the point, with `Pi.mulSingle_apply`.

| Lean name | Statement |
|---|---|
| `Pi.single_eq_same` | the value at $i$ is $x$ |
| `Pi.single_eq_of_ne` | the value at $i' \ne i$ is $0$ |
| `Pi.single_zero` | `Pi.single i 0` is the zero function |
| `Pi.single_eq_zero_iff` | `Pi.single i x` is zero if and only if $x = 0$ |
| `Pi.single_injective` | the map $x \mapsto$ `Pi.single i x` is injective |
| `Pi.single_comm` | for a constant family, the value at $j$ of the function at $i$ is the value at $i$ of the function at $j$ |
| `Pi.single_eq_single_iff` | two such functions are equal if and only if the points and values are equal, or both values are zero |
| `Pi.apply_single` | a map $f_j$ with $f_j(0) = 0$ commutes with the construction |
| `Pi.uncurry_single_single` | a function at $i$ with a value at $i'$ uncurries to the function at $(i, i')$ |

The proof of `Pi.single_eq_single_iff` shows the method. If $m = n = 0$, both sides are the zero function. Otherwise suppose $m \ne 0$. The left function is nonzero at $i$, so the right function is nonzero at $i$, so $i = j$, and the values at $i$ give $m = n$.

#### The support

The support of a function $f \colon I \to M$ is the set $\{x \mid f(x) \ne 0\}$. The module `Mathlib.Algebra.Notation.Support` defines it as `Function.support`, and the multiplicative support `Function.mulSupport` is the set where $f(x) \ne 1$. The membership lemma `Function.mem_support` is a simp lemma: $x \in \operatorname{supp} f \iff f(x) \ne 0$. The lemma `Function.compl_support` gives the complement as the zero set, and `Function.mulSupport_eq_preimage` gives the support as a preimage.

The library describes the support of each construction.

| Lean name | Statement |
|---|---|
| `Function.support_zero` | $\operatorname{supp} 0 = \emptyset$ |
| `Function.support_eq_empty_iff` | $\operatorname{supp} f = \emptyset \iff f = 0$ |
| `Function.support_nonempty_iff` | the support is nonempty if and only if $f \ne 0$ |
| `Function.support_const` | a nonzero constant has the whole type as support |
| `Function.support_subset_iff` | $\operatorname{supp} f \subseteq s \iff \forall x,\ f(x) \ne 0 \to x \in s$ |
| `Function.support_binop_subset` | if $\mathrm{op}(0, 0) = 0$, then $\operatorname{supp} \mathrm{op}(f, g) \subseteq \operatorname{supp} f \cup \operatorname{supp} g$ |
| `Function.support_comp_subset` | if $g(0) = 0$, then $\operatorname{supp}(g \circ f) \subseteq \operatorname{supp} f$ |
| `Function.support_comp_eq_preimage` | $\operatorname{supp}(g \circ f) = f^{-1}(\operatorname{supp} g)$ |
| `Function.support_prodMk` | the support of $x \mapsto (f(x), g(x))$ is $\operatorname{supp} f \cup \operatorname{supp} g$ |
| `Function.support_update_zero` | setting $f(x) = 0$ removes $x$ from the support |
| `Function.support_extend_zero` | for an injective $f$, extending $g$ by zero along $f$ has support $f(\operatorname{supp} g)$ |
| `Pi.support_single` | the support of `Pi.single i a` is $\emptyset$ if $a = 0$ and $\{i\}$ otherwise |

The proof of `Function.support_binop_subset` is one line. If $x$ is in neither support, then $f(x) = 0$ and $g(x) = 0$, so $\mathrm{op}(f(x), g(x)) = \mathrm{op}(0, 0) = 0$. The sum and the product of two functions are special cases, with $\mathrm{op}$ equal to $+$ or to $\cdot$, when $0 \cdot 0 = 0$.

The lemma `Function.ext_iff_support` gives a test for equality: $f = g$ if and only if the supports are equal and $f$ and $g$ agree on the support. The module `Mathlib.Algebra.Notation.FiniteSupport` adds one fact on finite supports: `Function.support_along_fiber_finite_of_finite` says that if $f$ on $I \times J$ has finite support, then for each $a$ the function $b \mapsto f(a, b)$ has finite support. The predicate there is `Function.HasFiniteSupport`.

#### The indicator function

Let $s$ be a subset of $\alpha$ and let $f \colon \alpha \to M$. The indicator `Set.indicator s f` is the function equal to $f$ on $s$ and to $0$ off $s$. It is in `Mathlib.Algebra.Notation.Indicator`, and the dot notation `s.indicator f` is common. The multiplicative form `Set.mulIndicator` uses $1$ off $s$. The definition uses classical logic, so it needs no decidability of membership. The lemma `Set.indicator_apply` gives the value as a conditional, with a decidability instance. The lemmas `Set.indicator_of_mem` and `Set.indicator_of_notMem` give the value on $s$ and off $s$. The classical characteristic function of $s$ is `Set.indicator s 1`.

| Lean name | Statement |
|---|---|
| `Set.indicator_univ` | $\mathbf 1_{\alpha} f = f$ |
| `Set.indicator_empty` | $\mathbf 1_{\emptyset} f = 0$ |
| `Set.indicator_zero` | $\mathbf 1_s 0 = 0$ |
| `Set.indicator_indicator` | $\mathbf 1_s(\mathbf 1_t f) = \mathbf 1_{s \cap t} f$ |
| `Set.support_indicator` | $\operatorname{supp}(\mathbf 1_s f) = s \cap \operatorname{supp} f$ |
| `Set.indicator_eq_self` | $\mathbf 1_s f = f \iff \operatorname{supp} f \subseteq s$ |
| `Set.indicator_eq_zero` | $\mathbf 1_s f = 0$ if and only if the support of $f$ is disjoint from $s$ |
| `Set.indicator_inter_support` | $\mathbf 1_{s \cap \operatorname{supp} f} f = \mathbf 1_s f$ |
| `Set.indicator_congr` | if $f = g$ on $s$, then $\mathbf 1_s f = \mathbf 1_s g$ |
| `Set.indicator_comp_of_zero` | if $g(0) = 0$, then $\mathbf 1_s (g \circ f) = g \circ \mathbf 1_s f$ |
| `Set.piecewise_eq_indicator` | the piecewise function of $f$ and $0$ is the indicator |
| `Set.indicator_eq_zero_or_self` | each value of $\mathbf 1_s f$ is $0$ or $f(a)$ |

Here is the proof of `Set.indicator_indicator`. Take a point $a$. If $a \in s \cap t$, both sides are $f(a)$. If $a \notin s$, the left side is $0$ and $a \notin s \cap t$, so the right side is $0$. If $a \in s$ and $a \notin t$, the left side is $\mathbf 1_t f(a) = 0$, and the right side is $0$. The proof of `Set.support_indicator` is the same case split, read through `Function.mem_support`.

The lemma `Set.indicator_rel_indicator` is a general tool. If a relation $r$ holds for $0$ and $0$, and holds for $f(a)$ and $g(a)$ when $a \in s$, then it holds for the values of the two indicators at $a$. Monotonicity of the indicator is a special case, with $r$ equal to $\le$. The lemmas `Set.indicator_preimage` and `Set.indicator_const_preimage` describe preimages: the preimage of a set under the indicator of a constant is one of $\alpha$, $s$, its complement and $\emptyset$. These facts make an indicator measurable when its set is measurable.

The module `Mathlib.Algebra.Group.Support` adds the facts on the support that need the operations of a monoid or a group. A sum has a smaller support: `Function.support_add` states $\operatorname{supp}(f + g) \subseteq \operatorname{supp} f \cup \operatorname{supp} g$, because $f(x) = 0$ and $g(x) = 0$ give $f(x) + g(x) = 0$. The lemmas `Function.support_sub` and `Function.support_nsmul` are the forms for a difference and a multiple, and `Function.support_neg` states that a negation has the same support. The multiplicative forms are `Function.mulSupport_mul`, `Function.mulSupport_div`, `Function.mulSupport_pow` and `Function.mulSupport_inv`.

The module `Mathlib.Algebra.Group.Indicator` gives the indicator its algebra. The indicator is additive in the function: `Set.indicator_add` states $\mathbf 1_s (f + g) = \mathbf 1_s f + \mathbf 1_s g$, and `Set.indicatorHom` packs it as an additive homomorphism $(\alpha \to M) \to (\alpha \to M)$. In the set it is additive on disjoint unions: `Set.indicator_union_of_disjoint` gives $\mathbf 1_{s \cup t} f = \mathbf 1_s f + \mathbf 1_t f$ when $s \cap t = \emptyset$, and `Set.indicator_union_add_inter` gives the general form $\mathbf 1_{s \cup t} f + \mathbf 1_{s \cap t} f = \mathbf 1_s f + \mathbf 1_t f$. The lemma `Set.indicator_self_add_compl` states $\mathbf 1_s f + \mathbf 1_{s^c} f = f$, and in a group `Set.indicator_compl` and `Set.indicator_sdiff` solve for the complement and for a difference of sets. The lemma `Set.indicator_singleton` identifies the indicator of a point with `Pi.single`, and `map_indicator` moves a homomorphism that preserves $0$ inside an indicator. Each lemma has a multiplicative form with `mulIndicator` in the name, such as `Set.mulIndicator_mul` and `Set.mulIndicatorHom`.

#### Common errors

1. The indicator and the support live in the namespaces Set and Function, not in the namespace Pi. Write `Set.indicator` and `Function.support`, or use dot notation on the set: `s.indicator f`.
2. `Pi.single` needs a decidable equality on the index type. In a proof with classical logic, two different decidability instances can make two copies of `Pi.single i x` that are not equal by `rfl`. Use `Pi.single.congr_simp` or `convert` to compare them.
3. `Set.indicator_apply` produces a conditional with a decidability instance on $a \in s$. When the goal has a fixed case, the lemmas `Set.indicator_of_mem` and `Set.indicator_of_notMem` are simpler than a case split.

### Exercises

1. (A) Use `Pi.mul_apply` to show that the pointwise product of functions $I \to M$ is associative when the multiplication of $M$ is associative.
2. (A) Prove that $\operatorname{supp}(\mathbf 1_s f) \subseteq s$ for each function $f$, from `Set.support_indicator`.
3. (A) Show that $\mathbf 1_s f + \mathbf 1_{s^c} f = f$ for a function into an additive monoid, by a case split on $a \in s$.
4. (B) Prove that $\mathbf 1_s f + \mathbf 1_t f = \mathbf 1_{s \cup t} f + \mathbf 1_{s \cap t} f$ for a function into an additive commutative monoid.
5. (B) Show that each function $f \colon \{1, \dots, n\} \to \mathbb{Z}$ is the sum of the functions `Pi.single i (f i)` over $i$, and compute the support of each term with `Pi.support_single`.
6. (C) Let $f \colon I \times J \to M$ have finite support. Prove that the set of $a \in I$ such that $b \mapsto f(a, b)$ is not the zero function is finite, and compare with `Function.support_curry`.

### Reference

<?reference?>
