---
title: Positivity, conjugation and projections in star-ordered rings
kind: api
modules:
  - Mathlib.Algebra.Order.Ring.Star
  - Mathlib.Algebra.Order.Star.Conjugate
  - Mathlib.Algebra.Order.Star.Orthogonal
  - Mathlib.Algebra.Order.Star.Projection
  - Mathlib.Algebra.Algebra.StrictPositivity
  - Mathlib.Algebra.Order.Star.Pi
  - Mathlib.Algebra.Order.Star.Prod
  - Mathlib.Algebra.Order.Star.Unitization
  - Mathlib.Algebra.Order.Star.Int
  - Mathlib.Algebra.Order.Star.Rat
  - Mathlib.Algebra.Order.Star.Real
  - Mathlib.Algebra.Order.Star.Conjneg
explains:
  E2: [StarOrderedRing.conjOrderHom, IsUnit.star_left_conjugate_le_conjugate, StarOrderedRing.conjUnitsOrderIso, isStarOrtho_iff_of_nonneg, IsStarOrtho.add_left_iff, IsStarProjection.le_iff_mul_eq_left, IsStarProjection.le_tfae, IsStrictlyPositive, IsStrictlyPositive.spectrum_pos, Unitization.inr_nonneg_iff]
  E1: auto
families: []
requires: [V06.C07, V06.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Positivity, conjugation and projections in star-ordered rings

### Overview

A star-ordered ring, from the section on star rings in Chapter 8, is a star ring with a partial order in which the nonnegative elements are the finite sums of elements $x^* x$, and $a \le b$ exactly when $b - a$ is such a sum. The positive semidefinite matrices and the nonnegative functions are the standard examples. This order is not compatible with multiplication in the usual sense: the product of two positive semidefinite matrices need not be positive semidefinite. The correct operation is conjugation, $a \mapsto r a r^*$, which keeps the order.

This section gives the API that uses this fact. It covers conjugation as an order map, the orthogonality of nonnegative elements, the order on star projections, the strictly positive elements, and the star orders on products, on the unitization and on the number systems. It needs the star rings of Chapter 8, the ordered rings of Chapter 7, and the projections and orthogonal pairs of Section 3.

### The library around it

#### Commutative star-ordered rings

The instance `StarOrderedRing.toIsOrderedRing` says that a commutative star-ordered semiring is an ordered semiring. Proof: if $0 \le a$ and $b \le c$, then $c - b$ is a sum of terms $x^* x$, and $a(x^* x) = x^* a x$ by commutativity, which is nonnegative by conjugation. In a noncommutative star-ordered ring the result fails. Nonnegative elements are self-adjoint, and the product $xy$ of two self-adjoint elements is self-adjoint only when $xy = yx$. So an ordered star-ordered ring has commuting nonnegative elements.

#### Conjugation

The map `StarOrderedRing.conjOrderHom r` is $x \mapsto r x r^*$ as a monotone map, by `StarOrderedRing.conjOrderHom_coe`. Proof of monotonicity: if $y - x = \sum s_i^* s_i$, then $r y r^* - r x r^* = \sum (s_i r^*)^* (s_i r^*)$. The map is multiplicative in $r$, by `StarOrderedRing.conjOrderHom_mul`, and `StarOrderedRing.conjOrderHom_one` says that $r = 1$ gives the identity. The bundled forms are `StarOrderedRing.conjOrderHomMulHom` and `StarOrderedRing.conjOrderHomMonoidHom`. Over a scalar ring $S$, `StarOrderedRing.conjPositiveLinearMap S r` is the same map as a positive $S$-linear map.

For a unit the map is an order isomorphism. `StarOrderedRing.conjUnitsOrderIso` sends a unit $u$ to the order isomorphism $x \mapsto u x u^*$, with inverse $x \mapsto u^{-1} x (u^{-1})^*$, by `StarOrderedRing.conjUnitsOrderIso_apply_symm_apply`. The lemmas give the cancellation rules:

| Lean name | Statement, for a unit $c$ |
| --- | --- |
| `IsUnit.star_left_conjugate_le_conjugate` | $c^* a c \le c^* b c \iff a \le b$ |
| `IsUnit.star_right_conjugate_le_conjugate` | $c a c^* \le c b c^* \iff a \le b$ |
| `IsLUB.conjugate_star_right_of_isUnit` | conjugation keeps least upper bounds |
| `IsGLB.conjugate_star_left_of_isUnit` | conjugation keeps greatest lower bounds |

For matrices, the first rule says that $A \preceq B$ exactly when $P^* A P \preceq P^* B P$ for an invertible $P$. This is Sylvester's congruence in the form of an order statement.

#### Orthogonality of nonnegative elements

Section 3 defines `IsStarOrtho a b` by the two equations $a b^* = 0$ and $b^* a = 0$. The module `Mathlib.Algebra.Order.Star.Orthogonal` proves that for nonnegative elements this is an order property. It needs the class `IsProperStar`, which says $x^* x = 0 \Rightarrow x = 0$. The theorem `isStarOrtho_iff_of_nonneg` says that for $0 \le a$, $a$ and $b$ are orthogonal exactly when $b^* a b = 0$ and $b a b^* = 0$. The form `isStarOrtho_iff_of_nonneg_of_isSelfAdjoint` uses the one condition $b a b = 0$ for a self-adjoint $b$.

Orthogonality to a sum of nonnegative elements splits. `IsStarOrtho.add_left_iff` says that for $0 \le a$ and $0 \le b$, $a + b$ is orthogonal to $c$ exactly when $a$ and $b$ are. Proof sketch: $c^* (a + b) c = c^* a c + c^* b c$ is a sum of two nonnegative terms, and it is $0$ exactly when both terms are $0$. The lemmas `IsStarOrtho.sum_left_iff` and `IsStarOrtho.sum_right_iff` extend this to finite sums. Orthogonality is also antitone: `IsStarOrtho.anti_left` says that $0 \le a \le b$ and $b \perp c$ give $a \perp c$. For star projections, `isStarProjection_add_iff` says that $p + q$ is a projection exactly when $p \perp q$, and `isStarProjection_sum_iff` gives the version for finite sums.

#### The order on star projections

The module `Mathlib.Algebra.Order.Star.Projection` describes $p \le q$ for two star projections. In the algebra of operators on a Hilbert space, $p \le q$ says that the range of $p$ is contained in the range of $q$. The theorem `IsStarProjection.le_tfae` lists the equivalent conditions, and the lemmas give each one alone:

| Lean name | Condition equivalent to $p \le q$ |
| --- | --- |
| `IsStarProjection.le_iff_mul_eq_left` | $p q = p$ |
| `IsStarProjection.le_iff_mul_eq_right` | $q p = p$ |
| `IsStarProjection.le_iff_conjugate_left_eq` | $p q p = p$ |
| `IsStarProjection.le_iff_conjugate_right_eq` | $q p q = p$ |
| `IsStarProjection.le_iff_isStarProjection_sub` | $q - p$ is a star projection |
| `IsStarProjection.le_iff_isStarOrtho_sub` | $p \perp (q - p)$ |
| `IsStarProjection.le_iff_isIdempotentElem_sub` | $q - p$ is idempotent |

Proof of one step: if $q - p$ is a star projection, then $p \le q$ because a star projection $e = e^* e$ is nonnegative. Conversely, in a unital ring, if $p \le q$, then conjugation by $1 - q$ gives $0 \le (1-q) p (1-q) \le (1-q) q (1-q) = 0$, so $p(1 - q) = 0$ by the proper star, and $p q = p$. The consequence `IsStarProjection.commute_of_le` says that comparable projections commute.

#### Strictly positive elements

The predicate `IsStrictlyPositive a` says $0 \le a$ and $a$ is a unit. For matrices this means positive definite. The lemma `IsStrictlyPositive.iff_of_unital` states the definition, and `IsStrictlyPositive.nonneg`, `IsStrictlyPositive.isUnit` and `IsStrictlyPositive.isSelfAdjoint` are the projections. The constant $1$ is strictly positive by `isStrictlyPositive_one`, and `isStrictlyPositive_algebraMap` gives the same for a positive scalar. `IsStrictlyPositive.smul` scales by a positive scalar, and `IsUnit.isStrictlyPositive_star_left_conjugate_iff` says that conjugation by a unit keeps strict positivity in both directions.

The spectrum of the section on the spectrum in Chapter 8 connects strict positivity to the scalars. If the algebra has `NonnegSpectrumClass 𝕜 A`, then `IsStrictlyPositive.spectrum_pos` says that each point of the spectrum of a strictly positive element is positive. Proof: the spectrum of a nonnegative element is nonnegative by the class, and $0$ is not in the spectrum of a unit by `Units.zero_notMem_spectrum`.

#### The standard examples

The integers, the rationals and the reals are star-ordered with the trivial star, by `Int.instStarOrderedRing`, `Rat.instStarOrderedRing` and `Real.instStarOrderedRing`. For $\mathbb{R}$ the proof uses square roots: a nonnegative $r$ is $\sqrt{r}\sqrt{r}$. For $\mathbb{Z}$ and $\mathbb{Q}$ there are no square roots, and the proof writes a nonnegative element as a sum of equal squares: $n = 1^2 + \dots + 1^2$ in $\mathbb{Z}$, and $p/q = pq \cdot (1/q)^2$ in $\mathbb{Q}$. The lemmas `Int.addSubmonoid_closure_range_mul_self` and `Rat.addSubmonoid_closure_range_mul_self` say that the sums of squares are exactly the nonnegative elements. The nonnegative types `NNRat` and `NNReal` are star-ordered by `NNRat.instStarOrderedRing` and `NNReal.instStarOrderedRing`.

Products of star-ordered rings are star-ordered with the coordinatewise order, by `Prod.instStarOrderedRing`, and finite products by `Pi.instStarOrderedRing`. The family must be finite: in an infinite product the coordinates of a nonnegative family can need more and more terms $x^* x$, and then the family is not a finite sum of such terms.

The unitization of the section on non-unital algebras in Chapter 8 is star-ordered when $A$ and $R$ are, and $R$ has a proper star. The order is defined by the cone `AddSubmonoid.starOrder` of sums of $x^* x$, and `Unitization.isPointed_starOrder` shows that this cone has no line through $0$, so it defines a partial order. The key step is `Unitization.of_mem_starOrder`: an element $(r, a)$ of the cone has $0 \le r$, and $0 \le a$ when $r = 0$. The lemma `Unitization.inr_nonneg_iff` says that $A$ keeps its order inside the unitization, and `Unitization.inl_nonneg_iff` says the same for $R$.

The module `Mathlib.Algebra.Order.Star.Conjneg` proves order facts about `conjneg f`, the function $x \mapsto \overline{f(-x)}$ of Section 4: `conjneg_nonneg` and `conjneg_pos` say that `conjneg` keeps nonnegativity and positivity of functions to a commutative star-ordered ring.

#### Common errors

1. A star-ordered ring is not an ordered ring. `mul_nonneg` does not apply to matrices, and the product of two nonnegative elements is nonnegative only when they commute. Use `StarOrderedRing.conjOrderHom`.
2. The orthogonality and projection lemmas need `IsProperStar`. A star ring with $x^* x = 0$ for some $x \neq 0$, such as the dual numbers with the trivial star and $x = \varepsilon$, does not satisfy it.
3. `IsStrictlyPositive` includes the unit condition, so it is not the same as $0 < a$. In $\mathbb{R}^2$ with the coordinatewise order, $(1, 0)$ satisfies $0 < (1, 0)$ but is not a unit.

### Exercises

1. (A) Check that $\begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix} \le \begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix}$ for the star projections with `IsStarProjection.le_iff_mul_eq_left`.
2. (A) Show that $2$ is strictly positive in $\mathbb{Q}$ with `IsStrictlyPositive.iff_of_unital`.
3. (B) Prove that conjugation $x \mapsto r x r^*$ is monotone from the definition of a star-ordered ring.
4. (B) Find two positive semidefinite $2 \times 2$ real matrices whose product is not symmetric.
5. (B) Let $p \le q$ be star projections. Prove $q p = p$ from $p q = p$ by applying the star.
6. (C) Prove `IsStarOrtho.add_left_iff` from `isStarOrtho_iff_of_nonneg`.

### Reference

<?reference?>
