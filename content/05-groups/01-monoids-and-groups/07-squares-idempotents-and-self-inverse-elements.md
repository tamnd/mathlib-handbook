---
title: Squares, idempotents and self-inverse elements
kind: api
modules:
  - Mathlib.Algebra.Group.Even
  - Mathlib.Algebra.Group.EvenFunction
  - Mathlib.Algebra.Group.Idempotent
  - Mathlib.Algebra.Group.SelfInv
explains:
  E2: [IsSquare.mul, Even.isSquare_pow, IsIdempotentElem.pow_eq, IsIdempotentElem.iff_eq_one_of_isUnit, isSelfInv_iff_sq_eq_one, Function.zero_of_even_and_odd, Function.Odd.mul_odd]
  E1: auto
families: []
requires: [V01.C04, V01.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Squares, idempotents and self-inverse elements

### Overview

This section collects four predicates on one element of a monoid or a group. An element $a$ is a *square* if $a = r r$ for some $r$. In additive notation the same predicate says $a = r + r$, and the element is *even*. An element $e$ is *idempotent* if $e e = e$. An element $a$ is *self-inverse* if $a^{-1} = a$. The fourth topic is a predicate on functions: a function $f$ is *even* if $f(-x) = f(x)$ and *odd* if $f(-x) = -f(x)$.

These predicates are small, but they appear in many places. The even integers form a subgroup of $\mathbb{Z}$, the squares of a commutative group form a subgroup, and an element of order $2$ is a self-inverse element. Idempotents give the projections of linear algebra and the decompositions of rings. The section states the closure properties of each predicate and the few results that need a proof.

### The library around it

#### Squares and even elements

**Definition (Square, even element).** Let $\alpha$ have a product. An element $a$ is a *square* if there is an $r$ with $a = r r$. Let $\alpha$ have an addition. An element $a$ is *even* if there is an $r$ with $a = r + r$.

The two predicates are `IsSquare a` and `Even a`, and `Even` is the additive copy of `IsSquare`. So each lemma comes in two forms with related names: `IsSquare.mul_self` and `Even.add_self`, `IsSquare.one` and `Even.zero`, `IsSquare.map` and `Even.map`. The definition uses $r r$ and not $r^2$, so that it needs only a product. The lemmas `isSquare_iff_exists_sq` and `even_iff_exists_two_nsmul` give the forms with $r^2$ and $2 \cdot r$ in a monoid.

**Theorem (Products of squares).** In a commutative semigroup, the product of two squares is a square.

*Proof.* Let $a = r r$ and $b = s s$. Then $a b = r r s s = (r s)(r s)$, by associativity and commutativity. $\square$

The lemma is `IsSquare.mul`. In a monoid that is not commutative it can fail. The closure under the other operations needs no commutativity: `IsSquare.pow` gives that each power of a square is a square, `IsSquare.inv` gives that the inverse of a square is a square in a division monoid, and `IsSquare.zpow` treats integer powers. The lemma `IsSquare.div` needs a commutative division monoid. A monoid homomorphism carries squares to squares, by `IsSquare.map`. The additive forms are `Even.add`, `Even.neg`, `Even.sub` and `Even.map`.

**Theorem (Even powers are squares).** Let $M$ be a monoid, let $a \in M$ and let $n$ be an even natural number. Then $a^n$ is a square.

*Proof.* Write $n = k + k$. Then $a^n = a^k a^k$ by the law $a^{k + k} = a^k a^k$. $\square$

The lemma is `Even.isSquare_pow`, and `Even.isSquare_zpow` is the form for an even integer exponent in a group. The lemma `IsSquare.sq` states that $r^2$ is a square. The type tags of the later sections exchange the two predicates: `isSquare_ofAdd_iff` states that `Multiplicative.ofAdd a` is a square exactly when $a$ is even, and `even_ofMul_iff` is the converse direction. The opposite monoid has the same squares, by `isSquare_op_iff`. The predicate `Odd` needs a semiring, and it is not in this section.

#### Idempotent elements

**Definition (Idempotent element).** Let $M$ have a product. An element $e$ is *idempotent* if $e e = e$.

The predicate is `IsIdempotentElem e`, and `isIdempotentElem_iff` unfolds it. The identity is idempotent, by `IsIdempotentElem.one`, and a multiplicative map carries idempotents to idempotents, by `IsIdempotentElem.map`. The product of two commuting idempotents is idempotent, by `IsIdempotentElem.mul_of_commute`: $(a b)(a b) = a a b b = a b$. In a commutative semigroup `IsIdempotentElem.mul` drops the hypothesis. The lemmas `IsIdempotentElem.mul_mul_self` and `IsIdempotentElem.mul_self_mul` absorb a repeated factor: $y e e = y e$.

**Theorem (Powers of an idempotent).** Let $e$ be idempotent in a monoid and let $n \neq 0$. Then $e^n = e$.

*Proof.* Induction on $n \geq 1$. For $n = 1$, $e^1 = e$. If $e^n = e$, then $e^{n+1} = e^n e = e e = e$. $\square$

The lemma is `IsIdempotentElem.pow_eq`, and `IsIdempotentElem.pow_succ_eq` is the form $e^{n+1} = e$.

**Theorem (Idempotent units).** Let $e$ be a unit of a monoid. Then $e$ is idempotent if and only if $e = 1$.

*Proof.* If $e e = e = e \cdot 1$, then cancel the unit $e$ on the left to get $e = 1$. The converse is $1 \cdot 1 = 1$. $\square$

The lemma is `IsIdempotentElem.iff_eq_one_of_isUnit`. In a cancellative monoid each element can be cancelled, and `IsIdempotentElem.iff_eq_one` states that $1$ is the only idempotent. So a group has exactly one idempotent. A monoid with zero has the second idempotent $0$, and Chapter 9 studies it. The subtype `{a // IsIdempotentElem a}` has the element $1$ by the instance `IsIdempotentElem.instOneSubtype`.

#### Self-inverse elements

**Definition (Self-inverse element).** Let $\alpha$ have an inverse. An element $a$ is *self-inverse* if $a^{-1} = a$.

The predicate is `IsSelfInv a`, with the additive copy `IsSelfNeg a` for $-a = a$. The lemma `isSelfInv_iff` unfolds it, and the instance `instDecidableIsSelfInvOfDecidableEq` makes it decidable on a type with decidable equality. The closure lemmas are `IsSelfInv.one`, `IsSelfInv.inv`, `IsSelfInv.pow` and `IsSelfInv.zpow`. The product of two self-inverse elements is self-inverse in a commutative division monoid, by `IsSelfInv.mul`; in a group in general it fails, since two reflections of the dihedral group $D_3$ have as product a rotation of order $3$. Conjugation preserves the predicate, by `IsSelfInv.conj`, and `isSelfInv_conj_iff` gives the equivalence in a group.

**Theorem (Self-inverse elements of a group).** Let $G$ be a group. An element $a$ is self-inverse if and only if $a^2 = 1$.

*Proof.* If $a^{-1} = a$, then $a^2 = a a = a a^{-1} = 1$. If $a a = 1$, then $a$ is a right inverse of $a$, so $a = a^{-1}$ by the uniqueness of inverses. $\square$

The lemma is `isSelfInv_iff_sq_eq_one`. So the self-inverse elements of a group are $1$ and the elements of order $2$. The pointwise forms for sets, with $s^{-1} = s$, are in Chapter 14.

#### Even and odd functions

The module `Mathlib.Algebra.Group.EvenFunction` defines `Function.Even f`, which states $f(-x) = f(x)$ for all $x$, and `Function.Odd f`, which states $f(-x) = -f(x)$. The domain needs only a negation. The lemmas `Function.Even.eq` and `Function.Odd.eq` extract the equation at a point. The closure lemmas follow the rule of signs:

| Lean name | Statement |
|---|---|
| `Function.Even.add` | even plus even is even |
| `Function.Odd.add` | odd plus odd is odd |
| `Function.Even.mul_even` | even times even is even |
| `Function.Even.mul_odd` | even times odd is odd |
| `Function.Odd.mul_odd` | odd times odd is even |
| `Function.Even.comp_odd` | an even function after an odd function is even |
| `Function.Odd.comp_odd` | an odd function after an odd function is odd |

The rule odd times odd is even has a one-line proof: $f(-x) g(-x) = (-f(x))(-g(x)) = f(x) g(x)$, where the last step uses $(-a)(-b) = a b$. So the lemma `Function.Odd.mul_odd` asks for the class `HasDistribNeg` on the values.

**Theorem (Even and odd functions).** Let $\beta$ be a commutative additive group in which $b + b = 0$ gives $b = 0$. A function $f : \alpha \to \beta$ that is both even and odd is zero.

*Proof.* For each $x$, $f(x) = f(-x) = -f(x)$, so $f(x) + f(x) = 0$, and then $f(x) = 0$. $\square$

The lemma is `Function.zero_of_even_and_odd`. The hypothesis on $\beta$ is the class `HasUniqueDiv β`: division by a nonzero natural number has at most one result, so $n b = n c$ with $n \neq 0$ gives $b = c$. The same hypothesis gives `Function.Odd.map_zero`, which states $f(0) = 0$ for an odd function, and `Function.Odd.sum_eq_zero`, which states that an odd function on a finite type with an involutive negation has sum $0$: the terms at $x$ and $-x$ cancel.

#### Common errors

1. A learner writes `Even n` and expects the integer or natural number definition with $n = 2 k$. The definition is $n = r + r$ for every type with an addition; the form with $2 \cdot r$ is `even_iff_exists_two_nsmul`.
2. A learner applies `IsSquare.mul` in a group that is not commutative. The lemma needs `CommSemigroup`. In a group that is not commutative, the product of two squares need not be a square, and the lemma gives no result.
3. A learner applies `Function.zero_of_even_and_odd` in a group such as $\mathbb{Z}/2$. There $b = -b$ for each $b$, each function is both even and odd, and the class `HasUniqueDiv` fails.

### Exercises

1. (A) Prove that the squares of a commutative group $G$ form a subgroup, and that it is the image of the homomorphism $x \mapsto x^2$.
2. (A) Let $e$ be idempotent in a ring. Prove that $1 - e$ is idempotent and that $e (1 - e) = 0$. Then use `IsIdempotentElem.map` to show that a ring homomorphism carries $e$ to an idempotent.
3. (B) Find all the idempotent elements of the monoid of maps $\{1, 2, 3\} \to \{1, 2, 3\}$ under composition, and describe them as the retractions onto their images.
4. (B) Prove that a finite group of even order has an element of order $2$: pair each element with its inverse and count the self-inverse elements.
5. (B) Prove that each function $f : \mathbb{R} \to \mathbb{R}$ is the sum of an even function and an odd function, in exactly one way.
6. (B) Prove that the set of squares of $S_3$ is the subgroup $A_3$, and that the set of squares of $S_4$ is the subgroup $A_4$.

### Reference

<?reference?>
