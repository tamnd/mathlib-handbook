---
title: Submonoids, closure and powers
kind: api
modules:
  - Mathlib.Algebra.Group.Submonoid.Defs
  - Mathlib.Algebra.Group.Submonoid.Basic
  - Mathlib.Algebra.Group.Submonoid.Membership
  - Mathlib.Algebra.Group.Submonoid.BigOperators
  - Mathlib.Algebra.Group.Submonoid.Finite
  - Mathlib.Algebra.Group.Submonoid.Finsupp
  - Mathlib.Algebra.Group.Irreducible.Indecomposable
explains:
  E2: [Submonoid.closure_le, Submonoid.closure_induction, Submonoid.closure_eq_one_union, Submonoid.mem_closure_singleton, Submonoid.exists_list_of_mem_closure, Submonoid.mem_sup, Submonoid.coe_iSup_of_directed, MonoidHom.eqOn_closureM, Submonoid.mem_closure_finset, isMulIndecomposable_id_univ]
  E1: auto
families: []
requires: [V01.C04, V03.C06, V04.C06, V05.C01, V05.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Submonoids, closure and powers

### Overview

A submonoid of a monoid $M$ is a subset that contains $1$ and is closed under multiplication. Submonoids appear wherever a group is not available: the multiplicative set of a localization, the positive cone of an ordered group, the set of products of a family of generators, and the powers of one element. In a group, a submonoid need not be a subgroup: the natural numbers are a submonoid of $(\mathbb{Z}, +)$ that is not closed under negation.

The seven modules of this section build the second layer of the tower of substructures, above the subsemigroups of the previous section. The layout is the same: the structure and its membership class, the complete lattice, the closure of a set with its induction principle, and the description of suprema. The membership module adds what is special to monoids: the powers of one element, products of lists, and the elements of a closure as products of generators. The last module studies indecomposable elements, the members of a family that are not products of two other members in a nontrivial way.

### The library around it

#### The structure and the bottom element

The module `Mathlib.Algebra.Group.Submonoid.Defs` defines `Submonoid M` for a type with `MulOneClass M`. A submonoid extends a subsemigroup by the field `Submonoid.one_mem'`, and `Submonoid.toSubsemigroup` forgets this field. The lemmas `Submonoid.one_mem` and `Submonoid.mul_mem` are the two axioms in their usual form, and `Submonoid.pow_mem` follows by induction on the exponent. The class `SubmonoidClass S M` collects the set-like types whose members contain $1$ and are closed under products. The general lemma `pow_mem` holds for each such type, and `SubmonoidClass.coe_pow` says that the coercion respects powers.

The submonoids form a complete lattice under inclusion, with meets given by intersections (`Submonoid.coe_inf`, `Submonoid.coe_iInf`). The bottom element is $\{1\}$, by `Submonoid.coe_bot` and `Submonoid.mem_bot`. This differs from the subsemigroup layer, where the bottom element is empty. Two submonoids are disjoint in the lattice when their intersection is $\{1\}$, by `Submonoid.disjoint_def`. The set `MonoidHom.eqLocusM f g` of points where two homomorphisms agree is a submonoid.

#### Closure

The module `Mathlib.Algebra.Group.Submonoid.Basic` defines `Submonoid.closure s`, the smallest submonoid that contains $s$. It satisfies the Galois connection `Submonoid.closure_le`:

$$\operatorname{closure}(s) \le S \iff s \subseteq S,$$

with the same proof as for subsemigroups. The Galois insertion is `Submonoid.gi`, and the standard consequences are `Submonoid.closure_mono`, `Submonoid.closure_union`, `Submonoid.closure_iUnion` and `Submonoid.closure_empty`. The supremum of two submonoids is the closure of the union, by `Submonoid.sup_eq_closure`.

The relation to the previous layer is `Submonoid.closure_eq_one_union`:

$$\operatorname{closure}_{\mathrm{mon}}(s) = \{1\} \cup \operatorname{closure}_{\mathrm{sgp}}(s).$$

Proof: the right side contains $s$ and $1$. It is closed under products, because a product with $1$ is the other factor, and the subsemigroup closure is closed. So it contains the submonoid closure. Conversely, $1$ is in the submonoid closure, and the submonoid closure is a subsemigroup that contains $s$, so it contains the subsemigroup closure. In the same way, $1$ does not change a closure: `Submonoid.closure_insert_one` and `Submonoid.closure_sdiff_singleton_one`.

The induction principle `Submonoid.closure_induction` has three cases: the generators, the element $1$, and products. The variant `Submonoid.closure_induction₂` handles two elements. In a monoid, `Submonoid.closure_induction_left` and `Submonoid.closure_induction_right` multiply by one generator at a time, on the left or on the right. As for subsemigroups, two homomorphisms that agree on $s$ agree on its closure, by `MonoidHom.eqOn_closureM`. The constructions `MonoidHom.ofClosureMEqTopLeft` and `MonoidHom.ofClosureMEqTopRight` build a homomorphism from a function that is multiplicative against generators.

#### Directed suprema

The module `Mathlib.Algebra.Group.Submonoid.Membership` starts with suprema. For a directed family $S_i$ indexed by a nonempty type, `Submonoid.coe_iSup_of_directed` states

$$\Big\uparrow \bigsqcup_i S_i = \bigcup_i S_i.$$

Proof sketch: the union contains $1$ because the index type is not empty. It is closed under products, because two elements lie in a common member of the family. So it is a submonoid, and it is the least upper bound. The hypothesis `[Nonempty ι]` is new in this layer. For the empty family the supremum is `⊥ = {1}`, but the union is empty. The membership form is `Submonoid.mem_iSup_of_directed`, and the form for sets of submonoids is `Submonoid.mem_sSup_of_directedOn`. Without directedness, `Submonoid.iSup_induction` reduces a property of the supremum to its members.

In a commutative monoid there is a simpler description of the supremum of two submonoids. The statement `Submonoid.mem_sup` says

$$x \in S \sqcup T \iff \exists y \in S,\ \exists z \in T,\ y z = x.$$

The set of such products contains $S$ and $T$ and is closed under products, because $(y z)(y' z') = (y y')(z z')$ in a commutative monoid. The lemma `Submonoid.sup_eq_range` writes the supremum as the range of the homomorphism $S \times T \to M$, $(y, z) \mapsto y z$.

#### Products of generators and powers

The same module describes the elements of a closure. In a monoid, every element of `Submonoid.closure s` is the product of a list of elements of $s$, by `Submonoid.exists_list_of_mem_closure`, and `Submonoid.closure_eq_image_prod` states the equality of sets. Proof sketch: the set of such products contains $s$ (lists of length one) and $1$ (the empty list), and it is closed under products (concatenate the lists). So it contains the closure, by `Submonoid.closure_le`. The other inclusion holds because the product of a list of members is a member. In a commutative monoid the list can be a multiset, by `Submonoid.exists_multiset_of_mem_closure`. The closure is also the range of the free monoid on $s$, by `Submonoid.closure_eq_mrange`.

The submonoid generated by one element is `Submonoid.powers x`, and `Submonoid.powers_eq_closure` identifies it with `Submonoid.closure {x}`. Its elements are the powers of $x$, by `Submonoid.mem_closure_singleton`:

$$y \in \operatorname{closure}\{x\} \iff \exists n \in \mathbb{N},\ x^n = y.$$

This follows from the description by lists: a list of copies of $x$ has the product $x^n$. In a commutative monoid, two generators give `Submonoid.mem_closure_pair`: the elements are the products $a^m b^n$. If $x^n = 1$ for some $n > 0$, then the powers of $x$ form a group, by `Submonoid.groupPowers`. If $n \mapsto x^n$ is injective, then `Submonoid.log` recovers the exponent, and `Submonoid.powLogEquiv` is an isomorphism from `Multiplicative ℕ` to the powers. An idempotent element has only the powers $1$ and $x$, by `IsIdempotentElem.coe_powers`.

#### Big operators and finite generation

The module `Mathlib.Algebra.Group.Submonoid.BigOperators` states that a submonoid is closed under the products of the big operators of Volume 3. The lemmas `list_prod_mem`, `multiset_prod_mem` and `prod_mem` hold for every `SubmonoidClass`. The product over a finite set of commuting elements is a member too, by `Submonoid.noncommProd_mem`. The coercion respects products, by `Submonoid.coe_finsetProd` and `Submonoid.coe_list_prod`. In a commutative monoid, the closure of a finite set $s$ has a closed form, `Submonoid.mem_closure_finset`:

$$x \in \operatorname{closure}(s) \iff \exists f : M \to \mathbb{N},\ \operatorname{support} f \subseteq s,\ \prod_{a \in s} a^{f(a)} = x.$$

The module `Mathlib.Algebra.Group.Submonoid.Finsupp` states the same with finitely supported exponents for an arbitrary family: `Submonoid.mem_closure_range_iff` writes the elements of the closure of the range of $f : \iota \to M$ as products $\prod_i f(i)^{a(i)}$ with $a : \iota \to_0 \mathbb{N}$. For a finite index type the exponents are a plain function, by `Submonoid.mem_closure_range_iff_of_fintype`.

The module `Mathlib.Algebra.Group.Submonoid.Finite` treats products of finitely many monoids. For a finite index type, the closure of a product of sets that contain $1$ is the product of the closures, by `Submonoid.closure_pi`. A submonoid of the product contains the product submonoid `Submonoid.pi Set.univ H` if and only if it contains the image of each factor under `MonoidHom.mulSingle`, by `Submonoid.pi_le_iff`.

#### Indecomposable elements

The module `Mathlib.Algebra.Group.Irreducible.Indecomposable` defines `IsMulIndecomposable v s i` for a family $v : \iota \to M$ and a set $s$ of indices. It holds when $i \in s$ and every factorization $v_i = v_j v_k$ with $j, k \in s$ has $v_j = 1$ or $v_k = 1$. For the identity family on all of $M$, this is irreducibility when the only unit is $1$, by `isMulIndecomposable_id_univ`: for $x \ne 1$, $x$ is indecomposable if and only if $x$ is irreducible. Proof sketch: with trivial units, "$a$ is a unit" means "$a = 1$", so the two definitions say the same thing.

The main result concerns a finite family and a homomorphism $f : M \to S$ into a linearly ordered cancellative commutative monoid. The set `IsMulIndecomposable.baseOf v f` collects the indecomposable members of the half space $\{i : 1 < f(v_i)\}$. Then `Submonoid.closure_image_isMulIndecomposable_baseOf` states that the base generates the same submonoid as the whole half space. The proof is a descent: a member that is not in the closure of the base and has the smallest value of $f$ would factor into two members with smaller values. For a commutative group and a family closed under inverses, `Subgroup.closure_image_isMulIndecomposable_baseOf` gives the analogue for subgroups. In the additive form, with the roots of a root system, the base is the set of simple roots.

#### Common errors

1. The directed supremum lemmas for submonoids need `[Nonempty ι]`, but the subsemigroup lemmas do not. For an empty family the supremum is `⊥ = {1}` and the union is empty. Supply the instance or use `Submonoid.mem_iSup_of_mem`, which needs no directedness.
2. `Submonoid.mem_sup` needs a commutative monoid. In a noncommutative monoid an element of $S \sqcup T$ can need an alternating product $s_1 t_1 s_2 t_2 \cdots$, and the lemma does not apply. Use `Submonoid.sup_eq_closure` and `Submonoid.closure_induction` there.
3. `Submonoid.powers x` and `Submonoid.closure {x}` are equal but not syntactically equal. The simp lemmas for powers use `Submonoid.mem_powers_iff`, and the lemmas for closures use `Submonoid.mem_closure_singleton`. Rewrite with `Submonoid.powers_eq_closure` to move from one to the other.

### Exercises

1. (A) Show that $\{n \in \mathbb{Z} : n \ge 0\}$ is an additive submonoid of $\mathbb{Z}$ but not an additive subgroup. Then show that the additive submonoid closure of $\{2, 3\}$ in $\mathbb{N}$ is $\mathbb{N} \setminus \{1\}$.
2. (A) Use `Submonoid.closure_eq_one_union` to prove that the submonoid closure of $s$ is the subsemigroup closure of $s$ when $1 \in s$.
3. (A) Prove that $x^n = 1$ with $n > 0$ implies $x^{n-1}$ is an inverse of $x$, and explain why this gives the group structure of `Submonoid.groupPowers`.
4. (B) Prove `Submonoid.mem_sup` for a commutative monoid. Then find two submonoids $S, T$ of a free monoid on two letters such that $S \sqcup T$ contains an element that is not of the form $y z$ with $y \in S$, $z \in T$.
5. (B) In the multiplicative monoid $\mathbb{N}$, show that the elements $x \ne 1$ that are indecomposable in the sense of `IsMulIndecomposable id Set.univ` are the primes. Why is $0$ not one of them? Which hypothesis of `isMulIndecomposable_id_univ` holds here?
6. (C) Let $v$ be the family of vectors $\pm e_1, \pm e_2, \pm(e_1 + e_2)$ in $\mathbb{Z}^2$, written additively, and let $f(a, b) = 2a + 3b$. Compute the half space $\{i : f(v_i) > 0\}$, its indecomposable members, and check the additive form of `Submonoid.closure_image_isMulIndecomposable_baseOf` by hand.

### Reference

<?reference?>
