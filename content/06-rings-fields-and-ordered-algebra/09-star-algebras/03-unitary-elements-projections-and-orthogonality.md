---
title: Unitary elements, projections and orthogonality
kind: api
modules:
  - Mathlib.Algebra.Star.Unitary
  - Mathlib.Algebra.Star.UnitaryStarAlgAut
  - Mathlib.Algebra.Star.StarProjection
  - Mathlib.Algebra.Star.Orthogonal
  - Mathlib.Algebra.Star.CHSH
explains:
  E2: [IsStarProjection.two_mul_sub_one_mem_unitary, Unitary.conjStarAlgAut_trans_conjStarAlgAut, Unitary.conjStarAlgAut_ext_iff, IsStarProjection.add, IsStarProjection.add_iff_isStarOrtho, IsStarOrtho.star_add_mul_add, Set.Pairwise.star_sum_mul_sum_of_isStarOrtho, CHSH_id, CHSH_inequality_of_comm, tsirelson_inequality]
  E1: auto
families: []
requires: [V06.C01, V06.C07, V06.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Unitary elements, projections and orthogonality

### Overview

Three kinds of elements of a star ring have names from operator theory. An element $u$ is *unitary* if $u^* u = 1 = u u^*$, so that $u^*$ is the inverse of $u$. An element $p$ is a *star projection* if $p^2 = p = p^*$. Two elements $p, q$ are *star orthogonal* if $p q^* = 0$ and $q^* p = 0$. On a Hilbert space, a unitary operator is an isometry onto the space, a star projection is the orthogonal projection onto a closed subspace, and two projections are star orthogonal when their ranges are orthogonal.

The five modules of this section develop these three notions in an arbitrary star ring, with no topology and no norm. The unitary elements form a group, and each unitary element gives an inner automorphism of the star algebra. The star projections are closed under the operations of a Boolean algebra when they commute. Orthogonality gives a Pythagoras identity. The last module proves the CHSH inequality and the Tsirelson bound, two inequalities from the theory of quantum measurements, as an application of the star ordered rings of Chapter 8.

### The library around it

#### The unitary submonoid

For a monoid $R$ with a star that reverses products, `unitary R` is the submonoid of unitary elements. Its membership lemma is `Unitary.mem_iff`: $U \in$ `unitary R` $\iff U^* U = 1 \wedge U U^* = 1$. The lemmas `Unitary.star_mul_self_of_mem` and `Unitary.mul_star_self_of_mem` extract the two halves. The submonoid is closed under the star, so the subtype has a star, and the instance `Unitary.instGroupSubtypeMemSubmonoidUnitary` makes it a group with inverse the star. The lemma `Unitary.star_eq_inv` says $U^* = U^{-1}$ in the subtype, and `Unitary.coe_star` moves the star through the coercion. When $R$ is commutative, the group is commutative, by `Unitary.instCommGroupSubtypeMemSubmonoidUnitary`.

Half of the condition is enough in two cases. For a unit $u$, `IsUnit.mem_unitary_iff_star_mul_self` says that $u^* u = 1$ suffices: then $u^* = u^{-1}$, so $u u^* = 1$ too. In a commutative monoid, `Unitary.mem_iff_star_mul_self` says the same for each element. In a general ring, one half does not suffice: the shift on the sequence space satisfies $S^* S = 1$ but $S S^* \neq 1$.

Each unitary element is a unit, and `Unitary.toUnits` is the injective group homomorphism to the units, by `Unitary.toUnits_injective`. In a group with zero, `Unitary.coe_inv` says that the inverse in the subtype is the inverse in $R$. For a group $G$ with a star, `unitarySubgroup G` is the subgroup of unitary elements, and `unitarySubgroupUnitsEquiv` identifies the unitary elements of the units of $M$ with the unitary elements of $M$.

The library computes the unitary elements of the standard constructions: `Prod.unitary_eq` for a product, `Pi.unitary_eq` for a function type, `MulOpposite.unitary_eq` for the opposite and `Units.unitary_eq` for the units. In each case the unitary elements are the elements with unitary components. In a ring with the trivial star and with no zero divisors, `Unitary.mem_iff_eq_one_or_eq_neg_one` says that the only unitary elements are $1$ and $-1$, because the condition is $u^2 = 1$, so $(u - 1)(u + 1) = 0$.

A star monoid homomorphism maps unitary elements to unitary elements. `Unitary.map f` is the restriction of $f$ to the unitary elements, as a star monoid homomorphism, and `Unitary.mapEquiv` is the same for an equivalence. `Unitary.map_injective` says that the restriction of an injective map is injective. A unitary scalar times a unitary element is unitary, by `Unitary.smul_mem_of_mem`.

A unitary element is normal, by `isStarNormal_of_mem_unitary`, because $u^* u = 1 = u u^*$. Unitary conjugation keeps the spectrum: `Unitary.spectrum_star_left_conjugate` says that $\sigma(U^* a U) = \sigma(a)$. The reason: conjugation by a unit is an algebra automorphism, and an algebra automorphism keeps the spectrum. An element commutes with a unitary $u$ if and only if conjugation by $u$ fixes it: `commute_unitary_iff_star_left_conjugate` says $u x = x u \iff u^* x u = x$.

A star projection gives a unitary element. `IsStarProjection.two_mul_sub_one_mem_unitary` says that $2p - 1$ is unitary. Proof: $2p - 1$ is self-adjoint, and $(2p - 1)^2 = 4p^2 - 4p + 1 = 1$. On a Hilbert space this is the reflection in the range of $p$.

#### Inner automorphisms

Conjugation by a unitary element is a star algebra automorphism. `Unitary.conjStarAlgAut S R` is the group homomorphism from `unitary R` to the group `R ≃⋆ₐ[S] R` of Section 1. The lemma `Unitary.conjStarAlgAut_apply` gives its value: the automorphism of $u$ sends $x$ to $u x u^*$. It respects the star, because $(u x u^*)^* = u x^* u^*$.

| Lean name | Statement |
|---|---|
| `Unitary.conjStarAlgAut_apply` | $\mathrm{Ad}_u(x) = u x u^*$ |
| `Unitary.conjStarAlgAut_symm` | $\mathrm{Ad}_u^{-1} = \mathrm{Ad}_{u^*}$ |
| `Unitary.conjStarAlgAut_trans_conjStarAlgAut` | $\mathrm{Ad}_{u_1}$ followed by $\mathrm{Ad}_{u_2}$ is $\mathrm{Ad}_{u_2 u_1}$ |
| `Unitary.conjStarAlgAut_ext_iff` | $\mathrm{Ad}_u = \mathrm{Ad}_v \iff \exists \alpha \in S,\ u = \alpha v$, for a central algebra |

The order in `Unitary.conjStarAlgAut_trans_conjStarAlgAut` follows the convention of `StarAlgEquiv.trans`: the first map acts first. So $\mathrm{Ad}_{u_2}(\mathrm{Ad}_{u_1}(x)) = u_2 u_1 x u_1^* u_2^* = \mathrm{Ad}_{u_2 u_1}(x)$, since $(u_2 u_1)^* = u_1^* u_2^*$.

The kernel of the map is the set of central unitary elements. The lemma `Unitary.conjStarAlgAut_ext_iff` makes this precise for an algebra with centre $S$, the class `Algebra.IsCentral`. Proof sketch: $\mathrm{Ad}_u = \mathrm{Ad}_v$ if and only if $v^{-1} u$ commutes with each $x$, that is, $v^{-1} u$ lies in the centre. The centre is the image of $S$, so $v^{-1} u = \alpha \cdot 1$ for some $\alpha \in S$. For matrices over $\mathbb{C}$, this says that two unitary matrices give the same conjugation exactly when they differ by a scalar.

#### Star projections

`IsStarProjection p` is a structure with two fields, `IsStarProjection.isIdempotentElem` and `IsStarProjection.isSelfAdjoint`. The lemma `isStarProjection_iff'` gives the form $p p = p \wedge p^* = p$. The elements $0$ and $1$ are projections, by `IsStarProjection.zero` and `IsStarProjection.one`. A projection is normal, by `IsStarProjection.isStarNormal`, and its powers are equal to it: `IsStarProjection.pow_eq` says $p^n = p$ for $n \neq 0$. A map in a type with `StarHomClass` and `MulHomClass` sends projections to projections, by `IsStarProjection.map`.

| Lean name | Statement |
|---|---|
| `IsStarProjection.one_sub` | $1 - p$ is a projection |
| `isStarProjection_one_sub_iff` | $1 - p$ is a projection $\iff p$ is |
| `IsStarProjection.mul_one_sub_self` | $p (1 - p) = 0$ |
| `IsStarProjection.add` | $p + q$ is a projection when $p q = 0$ |
| `IsStarProjection.mul` | $p q$ is a projection when $p$ and $q$ commute |
| `IsStarProjection.sub_of_mul_eq_left` | $q - p$ is a projection when $p q = p$ |
| `IsStarProjection.sub_iff_mul_eq_left` | $q - p$ is a projection $\iff p q = p$, with unique division by $2$ |
| `IsStarProjection.add_sub_mul_of_commute` | $p + q - p q$ is a projection when $p, q$ commute |

The proof of `IsStarProjection.add` uses only $p q = 0$. The star of $p q = 0$ gives $q p = 0$. Then $(p + q)^2 = p^2 + p q + q p + q^2 = p + q$, and $p + q$ is self-adjoint. For commuting projections, $p q$ is the meet and $p + q - p q$ is the join, so the commuting projections behave as a Boolean algebra. On a Hilbert space, $p \le q$ in the order of projections means $p q = p$, and $q - p$ is then the projection onto the orthogonal complement of the range of $p$ in the range of $q$.

The condition `HasUniqueDiv R` says that $n x = n y$ implies $x = y$ for $n \neq 0$. The converse direction of `IsStarProjection.sub_iff_mul_eq_left` needs it, because the proof ends with $2 (p q - p) = 0$.

#### Star orthogonality

The predicate `IsStarOrtho p q` is a structure with the fields $p q^* = 0$ and $q^* p = 0$. The notation `p ⋆⟂ q` is in the scope *StarRing*. For two self-adjoint elements, `IsSelfAdjoint.isStarOrtho_iff_mul_eq_zero` says that the condition is $p q = 0$: the second field is the star of the first. The relation is symmetric, `IsStarOrtho.symm`, and the lemmas `IsStarOrtho.add_left`, `IsStarOrtho.add_right`, `IsStarOrtho.mul_left`, `IsStarOrtho.sum_left` and their relatives say that it is closed under the ring operations in each argument. The lemma `IsStarOrtho.commute_star` says that $p$ commutes with $q^*$, because both products are $0$.

The main identity is Pythagoras. `IsStarOrtho.star_add_mul_add` says

$$(p + q)^* (p + q) = p^* p + q^* q \quad \text{when } p \perp q.$$

Proof: expand the left side to $p^* p + p^* q + q^* p + q^* q$. The field $q^* p = 0$ removes one cross term. The other cross term is $p^* q = (q^* p)^* = 0$. The mirror form `IsStarOrtho.add_mul_star_add` gives $(p + q)(p + q)^* = p p^* + q q^*$ with the other field. Induction over a finite set gives `Set.Pairwise.star_sum_mul_sum_of_isStarOrtho`: for a family that is orthogonal in pairs, $\left(\sum_i f_i\right)^* \left(\sum_i f_i\right) = \sum_i f_i^* f_i$.

Orthogonality connects to projections in three ways.

1. `IsStarProjection.isStarOrtho_one_sub` says that $p \perp 1 - p$, by `IsStarProjection.mul_one_sub_self`.
2. `IsStarProjection.add_iff_isStarOrtho` says that for projections $p, q$, the sum $p + q$ is a projection if and only if $p \perp q$. It needs `IsCancelAdd R` and `HasUniqueDiv R`. Proof of the hard direction: $(p + q)^2 = p + q$ gives $p q + q p = 0$. Multiply on the left by $p$ and on the right by $p$: $p q + p q p = 0$ and $p q p + q p = 0$. Cancellation gives $p q = q p$. So $2 p q = 0$, and $p q = 0$ by unique division.
3. `IsStarProjection.sum` says that a finite sum of projections that are orthogonal in pairs is a projection.

In a ring with a proper star, the condition is simpler. `IsProperStar R` says that $x^* x = 0$ implies $x = 0$. In such a ring, `isStarOrtho_self_iff` says that $p \perp p$ only for $p = 0$, and `IsStarNormal.isStarOrtho_iff_mul_eq_zero` says that for a normal $a$ that commutes with $b$, $a \perp b \iff a b = 0$. In the commutative case, `isStarOrtho_iff_mul_eq_zero_of_comm` gives $a \perp b \iff a b = 0$ for each pair. Each $C^*$-algebra has a proper star, by the $C^*$ identity $\|x^* x\| = \|x\|^2$.

#### The CHSH inequality

The module `Mathlib.Algebra.Star.CHSH` proves two inequalities about four elements $A_0, A_1, B_0, B_1$ of a star ordered ring. The structure `IsCHSHTuple A₀ A₁ B₀ B₁` says that each element is self-adjoint with square $1$, and that each $A_i$ commutes with each $B_j$. In quantum mechanics, the $A_i$ and $B_j$ are measurements with values $\pm 1$ of two separate observers.

First the identity. `CHSH_id` says: in a commutative ring, if the four squares are $1$, then $P = 2 - A_0 B_0 - A_0 B_1 - A_1 B_0 + A_1 B_1$ satisfies $P^2 = 4 P$. The proof is a computation with the ring normal form, after the replacement of each square by $1$.

Then `CHSH_inequality_of_comm`: in a commutative star ordered ring that is an ordered algebra over $\mathbb{R}$,

$$A_0 B_0 + A_0 B_1 + A_1 B_0 - A_1 B_1 \le 2.$$

Proof: $P$ is self-adjoint, and $P = \frac{1}{4} P^2 = \left(\frac{1}{2} P\right)^* \left(\frac{1}{2} P\right)$ by `CHSH_id`. In a star ordered ring each $x^* x$ is nonnegative, so $P \ge 0$, and this is the inequality. In a commutative model, such as random variables with values $\pm 1$, the bound $2$ holds.

Without commutativity the bound is larger. `tsirelson_inequality` says that in a star ordered ring that is an ordered star module over $\mathbb{R}$, the same sum is at most $\sqrt{2}^{\,3} \cdot 1 = 2\sqrt{2}$. Proof sketch: put $c = 1/\sqrt{2}$, $P = c(A_0 + A_1) - B_0$ and $Q = c(A_1 - A_0) + B_1$. Both are self-adjoint, and a computation with $A_i^2 = B_j^2 = 1$ and the commutation relations gives $P^2 + Q^2 = 4 - \sqrt{2}\,S$, where $S$ is the sum. The left side is nonnegative, so $S \le 4/\sqrt{2} = 2\sqrt{2}$. The helper `TsirelsonInequality.sqrt_two_inv_mul_self` gives $c^2 = 1/2$. The gap between $2$ and $2\sqrt{2}$ is the gap between classical and quantum correlations.

#### Common errors

1. The definition of `IsStarOrtho p q` does not use the products $p q$ and $q p$: the fields are $p q^* = 0$ and $q^* p = 0$. The two products $p q$ and $q p$ are the right test only for self-adjoint elements, by `IsSelfAdjoint.isStarOrtho_iff_mul_eq_zero`.
2. In `Unitary.conjStarAlgAut_trans_conjStarAlgAut`, the product on the right is $u_2 u_1$, not $u_1 u_2$, because `StarAlgEquiv.trans` applies its first argument first.
3. `CHSH_inequality_of_comm` needs a commutative ring. For non-commuting measurements, only `tsirelson_inequality` holds, with the bound $2\sqrt{2}$.

### Exercises

1. (A) Prove that the product of two unitary elements is unitary, directly from `Unitary.mem_iff`.
2. (A) Show that $p \perp 1 - p$ for a star projection $p$, and deduce that $1 = p + (1 - p)$ is a sum of orthogonal projections.
3. (B) Show that $2 p - 1$ is unitary for a star projection $p$, and that each self-adjoint unitary $u$ gives the projection $\frac{1}{2}(1 + u)$ when $2$ is invertible.
4. (B) Find two non-commuting star projections in the $2 \times 2$ complex matrices, and show that their product is not a projection.
5. (B) Prove `CHSH_id` by hand: expand $P^2$ and use $A_i^2 = B_j^2 = 1$ and commutativity.
6. (C) Find four $4 \times 4$ complex self-adjoint matrices with square $1$, with each $A_i$ commuting with each $B_j$, for which the CHSH sum has an eigenvalue $2\sqrt{2}$.

### Reference

<?reference?>
