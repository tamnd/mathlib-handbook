---
title: Idempotent semirings, Kleene algebras and quantales
kind: api
modules:
  - Mathlib.Algebra.Order.Kleene
  - Mathlib.Algebra.Order.Quantale
explains:
  E2: [IdemSemiring, KleeneAlgebra, add_eq_sup, kstar_le_of_mul_le_left, kstar_mul_kstar, kstar_eq_one, IsQuantale, Quantale.leftMulResiduation, Quantale.leftMulResiduation_le_iff_mul_le, Quantale.mul_iSup_distrib]
  E1: auto
families: []
requires: [V04.C03, V04.C04, V04.C06, V04.C08, V01.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Idempotent semirings, Kleene algebras and quantales

### Overview

In the earlier sections of this chapter the order and the operations are two structures that agree. In some semirings the order comes from the addition alone. If $a + a = a$ for each $a$, then the relation $a \le b$ defined by $a + b = b$ is a partial order, and $a + b$ is the supremum of $a$ and $b$. Such a semiring is *idempotent*. The languages over an alphabet, with union as the sum and concatenation as the product, are the main example. The binary relations on a set, with union and composition, are another one.

A Kleene algebra is an idempotent semiring with one more operation, the star $a^*$, which behaves as $1 + a + a^2 + \dots$. On languages it is the Kleene star of the theory of automata. A quantale is a complete lattice with a multiplication that distributes over all suprema. This section describes the two files that define these structures and their first lemmas.

### The library around it

#### Idempotent semirings

The class `IdemSemiring α` in `Mathlib.Algebra.Order.Kleene` asks for a semiring that is also a join semilattice with a bottom element, such that the sum is the supremum and $0$ is the bottom. The lemma `add_eq_sup` states $a + b = a \sqcup b$, and `add_idem` states $a + a = a$. The commutative form is `IdemCommSemiring`.

The class carries both the order and the addition, and asks that they agree. This is the pattern of the library for an order that can be defined from the operations: the definition is part of the data, so that a type with an order of its own, such as languages with inclusion, can use that order. To build an instance from a semiring alone, `IdemSemiring.ofSemiring` takes a proof of $a + a = a$ and defines $a \le b$ as $a + b = b$.

The order lemmas follow from `add_eq_sup`. The lemma `add_le_iff` states $a + b \le c \leftrightarrow a \le c \land b \le c$, which is the property of a supremum. The lemma `LE.le.add_eq_left` states that $b \le a$ gives $a + b = a$, and `add_eq_left_iff_le` is the equivalence. An idempotent semiring is canonically ordered, by the instance `IdemSemiring.toCanonicallyOrderedAdd`: if $a \le b$, then $b = a + b$. So the lemmas of Chapter 8 for canonically ordered monoids apply. Multiplication is monotone on both sides, by the instances `IdemSemiring.toMulLeftMono` and `IdemSemiring.toMulRightMono`. For the proof, $a \le b$ means $a + b = b$, so $c a + c b = c (a + b) = c b$, which means $c a \le c b$.

Numerals collapse in an idempotent semiring. The lemma `nsmul_eq_self` states $n \cdot a = a$ for $n \ne 0$, and `natCast_eq_one` states that the cast of each nonzero natural number is $1$. So an idempotent semiring that is not trivial does not have characteristic zero.

#### Kleene algebras

The class `KleeneAlgebra α` extends `IdemSemiring α` with an operation `KStar.kstar`, written $a^*$. Its axioms are:

- $1 \le a^*$, which is `KleeneAlgebra.one_le_kstar`;
- $a a^* \le a^*$ and $a^* a \le a^*$, which are `KleeneAlgebra.mul_kstar_le_kstar` and `KleeneAlgebra.kstar_mul_le_kstar`;
- if $a b \le b$, then $a^* b \le b$, which is `KleeneAlgebra.kstar_mul_le_self`;
- if $b a \le b$, then $b a^* \le b$, which is `KleeneAlgebra.mul_kstar_le_self`.

The first two axioms state that $a^*$ contains $1$ and is closed under multiplication by $a$. The last two state that $a^*$ is the least such element, in a form that uses only the order. The lemma `kstar_le_of_mul_le_left` gives the form that a proof uses most: if $1 \le b$ and $b a \le b$, then $a^* \le b$. The proof is one line from the axioms: $a^* = 1 \cdot a^* \le b a^* \le b$, with the monotonicity of the product and the last axiom.

The file derives the usual identities of the star. The lemma `le_kstar` states $a \le a^*$, and `pow_le_kstar` states $a^n \le a^*$ for each $n$. The lemma `kstar_mono` states that the star is monotone. The lemma `kstar_mul_kstar` states $a^* a^* = a^*$, and `kstar_idem` states $(a^*)^* = a^*$. The lemma `one_add_mul_kstar` states $1 + a a^* = a^*$, the unfolding equation of the star. On the special values, `kstar_zero` and `kstar_one` state $0^* = 1$ and $1^* = 1$, and `kstar_eq_one` states $a^* = 1 \leftrightarrow a \le 1$. The lemma `kstar_eq_self` states that $a^* = a$ exactly when $a a = a$ and $1 \le a$.

For the proof of `kstar_mul_kstar`, the inequality $a^* \le a^* a^*$ follows from $1 \le a^*$. For the other inequality, apply `mul_kstar_le` with $b = c = a^*$: the hypothesis $a^* a \le a^*$ is an axiom, so $a^* a^* \le a^*$.

The constructions carry the structure. The instances `Prod.instKleeneAlgebra` and `Pi.instKleeneAlgebraForall` give products and function types the componentwise star, as `Prod.fst_kstar` and `Pi.kstar_apply` state. The definition `Function.Injective.kleeneAlgebra` pulls the structure back along an injective map that keeps the operations. The languages of the volume on computability are a Kleene algebra by such an instance, with $L^*$ the set of the concatenations of finite lists of words of $L$.

#### Quantales

The class `IsQuantale α` in `Mathlib.Algebra.Order.Quantale` asks for a semigroup that is a complete lattice, with multiplication that distributes over each supremum on both sides:
$$x \cdot \textstyle\sup s = \sup_{y \in s} x y, \qquad (\sup s) \cdot y = \sup_{x \in s} x y.$$
These are the fields `IsQuantale.mul_sSup_distrib` and `IsQuantale.sSup_mul_distrib`. The structure `Quantale α` bundles a type with these classes. The additive form is `IsAddQuantale`. Examples are the sets of a monoid with the pointwise product, and the ideals of a commutative ring with the product of ideals.

The first lemmas are the indexed and binary forms. The lemma `Quantale.mul_iSup_distrib` states $x \cdot \bigsqcup_i f(i) = \bigsqcup_i x f(i)$, and `Quantale.mul_sup_distrib` states $x (y \sqcup z) = x y \sqcup x z$. The supremum of the empty set is $\bot$, so `Quantale.mul_bot` states $x \bot = \bot$. Distributivity over binary suprema gives monotonicity, so the instances `Quantale.instMulLeftMono` and `Quantale.instMulRightMono` hold.

#### Residuation

In a quantale, the map $z \mapsto z x$ keeps all suprema, so it has an upper adjoint in the sense of Chapter 6. The library defines it directly. The term `Quantale.leftMulResiduation x y` is $\sup \{z \mid z x \le y\}$, with the scoped notation $x \Rightarrow_l y$. The lemma `Quantale.leftMulResiduation_le_iff_mul_le` states the Galois connection:
$$z \le (x \Rightarrow_l y) \leftrightarrow z x \le y.$$
The proof of the direction from left to right uses the distributivity: $z x \le (\sup \{w \mid w x \le y\}) \cdot x = \sup \{w x \mid w x \le y\} \le y$. The other direction is the definition of a supremum. The right residuation `Quantale.rightMulResiduation` uses $x z$ in place of $z x$. In a commutative quantale the two agree, and the residuation plays the part of the implication of a Heyting algebra of Chapter 3, with multiplication in place of the infimum.

#### Common errors

1. In an `IdemSemiring`, the order is part of the data. A proof that $a \le b$ from $a + b = b$ needs `add_eq_sup` and the lemma *sup_eq_right* of Chapter 3, not a definition unfolding.
2. The star of a Kleene algebra is not defined as the supremum of the powers. The equation $a^* = \bigsqcup_n a^n$ needs a complete lattice and is proved for each type, as for languages. In a general Kleene algebra, use `pow_le_kstar` and `kstar_le_of_mul_le_left`.
3. A quantale need not have a unit for its multiplication, because the class asks only for a semigroup. Lemmas that use $1$, such as the axioms of a Kleene algebra, do not apply to a quantale without one.

### Exercises

1. (A) Prove `add_le_iff` from `add_eq_sup`.
2. (A) Show that the natural numbers with the usual addition are not an idempotent semiring, and find the axiom that fails.
3. (B) Prove `kstar_eq_one` from the axioms of a Kleene algebra and `kstar_le_of_mul_le_left`.
4. (B) Prove `kstar_idem`, with `kstar_mul_kstar` and `kstar_le_of_mul_le_left`.
5. (B) Show that the sets of a monoid, with union as the supremum and the pointwise product, satisfy the axioms of `IsQuantale`.
6. (C) Prove `Quantale.leftMulResiduation_le_iff_mul_le`, and deduce that $(x \Rightarrow_l y) x \le y$ for each $x$ and $y$.

### Reference

<?reference?>
