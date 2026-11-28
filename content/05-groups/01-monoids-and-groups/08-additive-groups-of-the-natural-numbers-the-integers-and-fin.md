---
title: The additive groups of the natural numbers, the integers and Fin n
kind: api
modules:
  - Mathlib.Algebra.Group.Nat.Defs
  - Mathlib.Algebra.Group.Nat.Even
  - Mathlib.Algebra.Group.Nat.Hom
  - Mathlib.Algebra.Group.Nat.Range
  - Mathlib.Algebra.Group.Nat.Units
  - Mathlib.Algebra.Group.Int.Defs
  - Mathlib.Algebra.Group.Int.Even
  - Mathlib.Algebra.Group.Int.Units
  - Mathlib.Algebra.Group.Fin.Basic
  - Mathlib.Algebra.Group.Fin.Tuple
  - Mathlib.Algebra.Group.ModEq
explains:
  E2: [Nat.even_mul, Nat.even_add, Nat.isUnit_iff, Int.isUnit_iff, AddMonoidHom.ext_nat, multiplesHom, AddCommGroup.modEq_iff_zsmul, Fin.neg_last]
  E1: auto
families: []
requires: [V02.C01, V02.C03, V02.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The additive groups of the natural numbers, the integers and Fin n

### Overview

The natural numbers, the integers and the types `Fin n` are the first examples of monoids and groups. Volume 2 builds these types and their arithmetic. The modules of this section give them the instances of the algebraic hierarchy of Chapter 1, and they collect the facts that need only the group structure: parity, units, homomorphisms out of $\mathbb{N}$, and congruence modulo an element.

The order of the instances matters for the reader. The type `ℕ` is a commutative monoid for $+$ and for $\times$, but it is not a group. The type `ℤ` is a commutative group for $+$. The type `Fin n` is a commutative group for addition modulo $n$ when $n \neq 0$. Each result below uses the weakest of these structures that it needs.

### The library around it

#### The instances

The module `Mathlib.Algebra.Group.Nat.Defs` gives `Nat.instAddCancelCommMonoid` and `Nat.instCommMonoid`, and the module `Mathlib.Algebra.Group.Int.Defs` gives `Int.instAddCommGroup` and `Int.instCommMonoid`. The smaller instances, such as `Nat.instAddMonoid` and `Int.instSemigroup`, are shortcuts: they let Lean find a small structure without a long search through the hierarchy. Both types also have `HasUniqueDiv`, by `Nat.instHasUniqueDiv` and `Int.instHasUniqueDiv`, and `ℕ` has `HasUniqueRoots`, by `Nat.instHasUniqueRoots`.

The scalar actions agree with the products. The lemma `Nat.nsmul_eq_mul` states $m \cdot n = m n$ for the action of $\mathbb{N}$ on itself. The lemmas `Int.nsmul_eq_mul` and `Int.zsmul_eq_mul` state the same for the actions of $\mathbb{N}$ and $\mathbb{Z}$ on $\mathbb{Z}$. They are the bridge from the notation `n • a` of a general additive monoid to the product of numbers.

For `Fin n`, the module `Mathlib.Algebra.Group.Fin.Basic` gives `Fin.addCommSemigroup` for each $n$, and `Fin.addCommMonoid` and `Fin.addCommGroup` under `[NeZero n]`, since `Fin 0` is empty and has no zero. Addition and negation are modulo $n$. The negation is involutive for each $n$, by `Fin.instInvolutiveNeg`, and addition cancels, by `Fin.instIsCancelAdd`.

#### Parity

The modules `Mathlib.Algebra.Group.Nat.Even` and `Mathlib.Algebra.Group.Int.Even` study `Even n` for numbers. The predicate is the general one of the section on squares: $n = r + r$. The lemmas `Nat.even_iff` and `Int.even_iff` give the computable form $n \bmod 2 = 0$, and `Nat.not_even_iff` gives $n \bmod 2 = 1$. The instances `Nat.instDecidablePredEven` and `Int.instDecidablePredEven` make parity decidable, so the tactic decide proves `Even 10`.

**Theorem (Parity of sums and products).** For natural numbers $m$ and $n$: $m + n$ is even if and only if $m$ and $n$ have the same parity, and $m n$ is even if and only if $m$ or $n$ is even.

*Proof.* Reduce modulo $2$. Each number is $0$ or $1$ modulo $2$. Then check the four cases for $m + n$ and for $m n$. $\square$

The lemmas are `Nat.even_add` and `Nat.even_mul`. The statement of `Nat.even_add` is an equivalence of equivalences: `Even (m + n) ↔ (Even m ↔ Even n)`. The integer forms are `Int.even_add` and `Int.even_mul`, and `Int.even_sub` has no hypothesis, but `Nat.even_sub` needs $n \leq m$ because of truncated subtraction. The lemma `Nat.even_pow` states that $m^n$ is even if and only if $m$ is even and $n \neq 0$. The lemmas `Nat.even_mul_succ_self` and `Nat.even_mul_pred_self` state that $n (n + 1)$ and $n (n - 1)$ are even. The cast is compatible: `Int.even_natCast` states that $(n : \mathbb{Z})$ is even exactly when $n$ is even. The lemmas `Nat.two_mul_div_two_of_even` and `Int.two_mul_ediv_two_of_even` recover $n$ from $n / 2$. The predicate `Odd` needs the semiring structure, and it is not in this section.

#### Units

**Theorem (Units of the natural numbers and the integers).** The only unit of $(\mathbb{N}, \times)$ is $1$. The units of $(\mathbb{Z}, \times)$ are $1$ and $-1$.

*Proof.* If $m n = 1$ in $\mathbb{N}$, then $m \neq 0$ and $n \neq 0$, so $m \leq m n = 1$ and $m = 1$. In $\mathbb{Z}$, take absolute values: $|u| |v| = 1$ in $\mathbb{N}$, so $|u| = 1$ and $u = \pm 1$. Both $1$ and $-1$ are their own inverses. $\square$

The lemmas are `Nat.isUnit_iff` and `Int.isUnit_iff`. The forms for the group of units are `Nat.units_eq_one` and the instance `Nat.unique_units`. The additive form `Nat.isAddUnit_iff` states that $0$ is the only element of $\mathbb{N}$ with an additive inverse, and `Nat.unique_addUnits` is the matching instance. For the integers, the module `Mathlib.Algebra.Group.Int.Units` has a family of lemmas with the pattern `Int.isUnit_*`. The lemma `Int.isUnit_iff_natAbs_eq` states $|u| = 1$, `Int.isUnit_mul_self` states $u u = 1$, and `Int.isUnit_eq_or_eq_neg` states that two units are equal or opposite. The lemma `Int.mul_eq_one_iff_eq_one_or_neg_one` solves $u v = 1$ in $\mathbb{Z}$.

#### Homomorphisms out of the natural numbers

**Theorem (Universal property of $\mathbb{N}$).** Let $M$ be an additive monoid. Each element $x \in M$ gives a unique additive monoid homomorphism $f : \mathbb{N} \to M$ with $f(1) = x$, namely $f(n) = n \cdot x$.

*Proof.* The map $n \mapsto n \cdot x$ is additive, since $(m + n) \cdot x = m \cdot x + n \cdot x$. If $f$ is additive and $f(1) = x$, then induction on $n$ gives $f(n + 1) = f(n) + f(1) = n \cdot x + x$. $\square$

The lemma `AddMonoidHom.ext_nat` gives the uniqueness: two homomorphisms that agree at $1$ are equal. The lemma `AddMonoidHom.apply_nat` states $f(n) = n \cdot f(1)$, and `ext_nat'` is the form for a class of homomorphisms. The equivalence `multiplesHom M` from $M$ to the type `ℕ →+ M` packs the whole theorem. When $M$ is commutative, `multiplesAddHom M` is an additive equivalence, since the homomorphisms $\mathbb{N} \to M$ then form an additive monoid. The multiplicative forms are `powersHom` and `powersMulHom`. They use the type `Multiplicative ℕ`, which is $\mathbb{N}$ with its addition written as a product, and the section on type tags explains this tag. The lemmas `MonoidHom.ext_mnat` and `MonoidHom.apply_mnat` are the matching forms.

The small module `Mathlib.Algebra.Group.Nat.Range` splits a range: `Finset.range_add` states $\{0, \dots, a + b - 1\} = \{0, \dots, a - 1\} \cup (a + \{0, \dots, b - 1\})$, and `Finset.disjoint_range_addLeftEmbedding` states that the two parts are disjoint.

#### Congruence modulo an element

The module `Mathlib.Algebra.Group.ModEq` defines a congruence in each commutative additive monoid. The notation is `a ≡ b [PMOD p]`, and the definition is `AddCommGroup.ModEq p a b`. In a group the statement is that $b - a$ is an integer multiple of $p$.

**Theorem (Congruence in a group).** Let $G$ be a commutative additive group. Then $a \equiv b \pmod p$ if and only if $b - a = m \cdot p$ for some $m \in \mathbb{Z}$.

*Proof.* The definition in a monoid states $m \cdot p + a = n \cdot p + b$ for some natural numbers $m$ and $n$, by `AddCommGroup.modEq_iff_nsmul`. In a group, subtract: $b - a = (m - n) \cdot p$. Conversely, write an integer multiple as a difference of two natural multiples. $\square$

The lemma is `AddCommGroup.modEq_iff_zsmul`. The lemma `AddCommGroup.modEq_iff_eq_add_zsmul` gives the form $b = a + z \cdot p$. The relation is an equivalence relation, by `AddCommGroup.modEq_refl`, `AddCommGroup.ModEq.symm` and `AddCommGroup.ModEq.trans`, and it is compatible with the operations: `AddCommGroup.ModEq.add`, `AddCommGroup.ModEq.neg` and `AddCommGroup.ModEq.sub`. The lemma `AddCommGroup.modEq_zero` states that congruence modulo $0$ is equality. The lemmas `AddCommGroup.nsmul_modEq_nsmul` and `AddCommGroup.zsmul_modEq_zsmul` cancel a common factor, and they need `HasUniqueDiv`. The congruence is used in the real numbers, where $a \equiv b \pmod{2\pi}$ compares angles. The congruences `Nat.ModEq` and `Int.ModEq` of Volume 2 are different definitions, with a notation `[MOD n]` and `[ZMOD n]`.

#### Fin n and tuples

The order of `Fin n` and the addition modulo $n$ do not agree, so the lemmas of `Mathlib.Algebra.Group.Fin.Basic` describe the overflow. For example `Fin.add_lt_left_iff` states that $a + b < a$ exactly when the reverse of $b$ is less than $a$, and `Fin.coe_sub_one` gives the value of $a - 1$ as a natural number: $n$ if $a = 0$, and $a - 1$ otherwise. The lemma `Fin.neg_last` states $-n = 1$ in `Fin (n + 1)`: the last element is $-1$. The reversal $a \mapsto n - 1 - a$ exchanges addition and subtraction, by `Fin.rev_add` and `Fin.rev_sub`.

The module `Mathlib.Algebra.Group.Fin.Tuple` treats tuples `Fin n → α` with the pointwise operations. The lemmas with the pattern `Matrix.cons_*` compute with the notation `![x, y, z]`: `Matrix.cons_add_cons` states that the sum of two tuples is the tuple of the sums, and `Matrix.cons_eq_zero_iff` states that a tuple is zero exactly when its head and its tail are zero. The lemmas `Fin.insertNth_mul` and `Fin.insertNth_add` state that inserting an entry is compatible with the operations, and `Fin.insertNth_zero_right` turns the insertion into `Pi.single`.

#### Common errors

1. A learner writes `n - m` in `ℕ` and applies a lemma for groups. Subtraction on `ℕ` is truncated, `ℕ` is not a group, and the lemmas for `ℤ` such as `Int.even_sub` do not apply. Cast to `ℤ` first, or use the form with a hypothesis $n \leq m$.
2. A learner asks for `AddCommGroup (Fin n)` with a variable $n$. The instance needs `[NeZero n]`, and Lean does not find it for an arbitrary $n$. Write `Fin (n + 1)`, or add the hypothesis `[NeZero n]`.
3. A learner confuses `a ≡ b [PMOD p]` with `a ≡ b [ZMOD n]`. The first is `AddCommGroup.ModEq` in any commutative additive monoid. The second is `Int.ModEq`, and the two have different lemmas.

### Exercises

1. (A) Prove `Even (n * (n + 1))` for each natural number $n$ from `Nat.even_mul` and `Nat.even_add_one`.
2. (A) Use `Int.isUnit_iff` to show that the group of units of $\mathbb{Z}$ has exactly two elements, and that it is isomorphic to `Fin 2` with addition.
3. (B) Prove that two additive homomorphisms $\mathbb{Z} \to G$ that agree at $1$ are equal, by reduction to `AddMonoidHom.ext_nat`.
4. (B) Let $G$ be a commutative additive group and $p \in G$. Prove that $a \equiv b \pmod p$ holds exactly when $a$ and $b$ have the same image in the quotient of $G$ by the subgroup generated by $p$.
5. (B) Prove that in `Fin (n + 1)` the map $a \mapsto -a$ fixes $0$, and that for $n + 1$ odd it fixes no other element.
6. (C) Prove that `multiplesHom ℕ` sends $x$ to the map $n \mapsto n x$. Deduce that the monoid of additive endomorphisms of $\mathbb{N}$, under composition, is isomorphic to $(\mathbb{N}, \times)$.

### Reference

<?reference?>
