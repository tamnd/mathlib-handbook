---
title: Torsion-free monoids, unique products and affine monoids
kind: api
modules:
  - Mathlib.Algebra.Group.Torsion
  - Mathlib.Algebra.Group.Pi.Torsion
  - Mathlib.Algebra.Group.UniqueProds.Basic
  - Mathlib.Algebra.Group.UniqueProds.VectorSpace
  - Mathlib.Algebra.FreeMonoid.UniqueProds
  - Mathlib.Algebra.FreeAbelianGroup.UniqueSums
  - Mathlib.Algebra.AffineMonoid.Basic
  - Mathlib.Algebra.AffineMonoid.Embedding
  - Mathlib.Algebra.AffineMonoid.Irreducible
  - Mathlib.Algebra.AffineMonoid.UniqueSums
explains:
  E2: [pow_eq_one_iff_left, IsMulTorsionFree.pow_right_inj, inv_eq_self, UniqueProds.toIsCancelMul, UniqueProds.of_injective_mulHom, TwoUniqueProds.of_covariant_left, irreducible_subset_of_submonoidClosure_eq_top, finite_irreducible, AffineAddMonoid.embedding_injective]
  E1: auto
families: []
requires: [V05.C01, V05.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Torsion-free monoids, unique products and affine monoids

### Overview

The earlier sections of this chapter study elements of finite order. This section studies the opposite condition. A monoid is *torsion-free* when the map $a \mapsto a^n$ cannot identify two commuting elements, for each $n \neq 0$. In a group this says that $1$ is the only element of finite order. The library has two classes for this idea, a weak one and a strong one, and a long list of cancellation lemmas for powers.

The second subject is the *unique product property*. A magma $G$ has unique products when, for any two nonempty finite subsets $A$ and $B$, some element of $A B$ has exactly one expression $a b$ with $a \in A$ and $b \in B$. Ordered groups have this property, and so do the free monoids, the free abelian groups and the vector spaces over $\mathbb{Q}$. The property is the combinatorial input for the theorem that a monoid algebra over a domain has no zero divisors.

The third subject is the *affine monoids*: the commutative monoids that are finitely generated, cancellative and torsion-free. The monoid $\mathbb{N}^n$ and the numerical monoids are examples. The library proves that an affine monoid embeds in $\mathbb{Z}^n$, that it has only finitely many irreducible elements, and that it has unique sums. Finite generation is the subject of the section on finitely generated groups in this chapter, and the irreducible elements come from Chapter 1.

### The library around it

#### Two torsion-free classes

The classes live in `Mathlib.Algebra.Group.Monoid`, and the module `Mathlib.Algebra.Group.Torsion` holds their lemmas. The class `IsMulTorsionFree M` says that $a^n = b^n$ implies $a = b$ when $n \neq 0$ and $a$ and $b$ commute. The class `HasUniqueRoots M` drops the condition that $a$ and $b$ commute: the map $a \mapsto a^n$ is injective for each $n \neq 0$. The two unfold by `isMulTorsionFree_iff` and `hasUniqueRoots_iff`, and the field `HasUniqueRoots.pow_left_injective` gives the injectivity. The additive forms are `IsAddTorsionFree` and `HasUniqueDiv`, with $n \cdot a$ in place of $a^n$.

Unique roots imply torsion-free, by the instance `instIsMulTorsionFreeOfHasUniqueRoots`. In a commutative monoid the two classes agree, by `IsMulTorsionFree.hasUniqueRoots`. In a noncommutative group they differ: exercise 6 gives a torsion-free group in which two different elements have the same square. So a lemma about $a^n = b^n$ for arbitrary $a$ and $b$ needs `HasUniqueRoots`, and the same lemma for commuting elements needs only `IsMulTorsionFree`.

| Lean name | Statement |
| --- | --- |
| `pow_left_inj` | $a^n = b^n \iff a = b$ for $n \neq 0$, with unique roots |
| `Commute.pow_left_inj` | the same for commuting $a$, $b$ in a torsion-free monoid |
| `zpow_left_inj` | $a^n = b^n \iff a = b$ for $n \in \mathbb{Z}$, $n \neq 0$, in a group with unique roots |
| `pow_eq_one_iff` | $a^n = 1 \iff a = 1 \lor n = 0$ |
| `pow_eq_one_iff_left` | $a^n = 1 \iff a = 1$ for $n \neq 0$ |
| `sq_eq_one` | $a^2 = 1 \iff a = 1$ |
| `IsMulTorsionFree.zpow_eq_one_iff` | $a^n = 1 \iff a = 1 \lor n = 0$ for $n \in \mathbb{Z}$ |
| `inv_eq_self` | $a^{-1} = a \iff a = 1$ |
| `isSelfInv_iff_eq_one` | $a$ is its own inverse iff $a = 1$ |

The proof of `pow_eq_one_iff_left` is one line. The elements $a$ and $1$ commute, and $1^n = 1$. So $a^n = 1^n$ gives $a = 1$ by the definition of the class. Then `inv_eq_self` follows: from $a^{-1} = a$ the product gives $a^2 = a a^{-1} = 1$, and `sq_eq_one` gives $a = 1$. The names `self_eq_inv`, `inv_ne_self` and `self_ne_inv` are the other forms of the same fact.

The exponent can also cancel. In a cancellative torsion-free monoid, `IsMulTorsionFree.pow_right_inj` states $a^n = a^m \iff n = m$ for $a \neq 1$. The proof: suppose $n < m$. Then $a^n \cdot 1 = a^n \cdot a^{m - n}$, so cancellation gives $a^{m - n} = 1$, and `pow_eq_one_iff_left` gives $a = 1$, a contradiction. The injective form is `IsMulTorsionFree.pow_right_injective`, and the integer forms are `IsMulTorsionFree.zpow_right_inj` and `IsMulTorsionFree.zpow_right_injective`.

Unique roots also give a test for commutation. In a group with unique roots, `Commute.of_zpow_left` states that $a^n$ commutes with $b$ only when $a$ commutes with $b$, for $n \neq 0$. The reason: the element $b a b^{-1}$ has $n$th power $b a^n b^{-1} = a^n$, so unique roots give $b a b^{-1} = a$. The variants `Commute.of_zpow_right` and `Commute.of_zpow_zpow` put the power on the other side or on both sides.

The module `Mathlib.Algebra.Group.Pi.Torsion` has four instances: a product of torsion-free monoids is torsion-free, by `Pi.instIsMulTorsionFree`, and a product of monoids with unique roots has unique roots, by `Pi.instHasUniqueRootsForall`. The additive forms are `Pi.instIsAddTorsionFree` and `Pi.insthasUniqueDivForall`. The proof is pointwise in each case. Chapter 11 relates the torsion-free condition to the torsion subgroup of a commutative group.

#### Unique products

The module `Mathlib.Algebra.Group.UniqueProds.Basic` works with a type that has only a multiplication. For finite sets $A$ and $B$, the predicate `UniqueMul A B a0 b0` says: each pair $(a, b) \in A \times B$ with $a b = a_0 b_0$ is the pair $(a_0, b_0)$. It does not require $a_0 \in A$. With membership, `UniqueMul.iff_existsUnique` turns it into a unique existence statement. The lemma `UniqueMul.mt` gives the contrapositive form, which is the form for use: if $a \in A$, $b \in B$ and $(a, b) \neq (a_0, b_0)$, then $a b \neq a_0 b_0$. A unique pair stays unique in smaller sets, by `UniqueMul.mono`, and singletons always give a unique pair, by `UniqueMul.of_card_le_one`.

The class `UniqueProds G` asks for a unique pair for each two nonempty finite sets. Its field is `UniqueProds.uniqueMul_of_nonempty`. The class `TwoUniqueProds G` asks for two different unique pairs when $|A| \cdot |B| > 1$, with the field `TwoUniqueProds.uniqueMul_of_one_lt_card`. The stronger class gives the weaker, by the instance `TwoUniqueProds.toUniqueProds`. For a group the converse holds, by `UniqueProds.toTwoUniqueProds_of_group`. For a cancellative semigroup it is sufficient to take $A = B$, by `UniqueProds.of_same`. The additive classes are `UniqueSums` and `TwoUniqueSums`, with `UniqueAdd` in place of `UniqueMul`.

The property forces cancellation. By `UniqueProds.toIsCancelMul`, a magma with unique products is cancellative. The proof for the left side: suppose $a b = a c$. Take $A = \{a\}$ and $B = \{b, c\}$. There is a unique pair, and it is $(a, b)$ or $(a, c)$. In both cases the other pair has the same product, so the two pairs are equal and $b = c$. In the same way, a group with an element $g \neq 1$ of finite order does not have unique products, as exercise 3 shows. So the property is a strong form of the torsion-free condition.

The property passes back along injective maps. By `UniqueProds.of_injective_mulHom`, if $f : H \to G$ is an injective multiplicative map and $G$ has unique products, then $H$ has unique products. The proof: for finite $A$ and $B$ in $H$, take the images $f(A)$ and $f(B)$ in $G$ and a unique pair $(f(a_0), f(b_0))$ there. If $a b = a_0 b_0$ in $H$, then $f(a) f(b) = f(a_0) f(b_0)$, so $f(a) = f(a_0)$ and $f(b) = f(b_0)$, and injectivity ends the proof. The lemma `UniqueProds.of_mulHom` weakens the injectivity to what the proof uses. The same results hold for `TwoUniqueProds`, for example `TwoUniqueProds.of_injective_mulHom`. An isomorphism gives an equivalence, by `MulEquiv.uniqueProds_iff`.

The main source of examples is an order. By `TwoUniqueProds.of_covariant_left`, a left cancellative linearly ordered magma in which right multiplication is strictly monotone has two unique products. Here is the idea for one pair in a linearly ordered cancellative commutative monoid. Let $a_0$ be the least element of $A$ and $b_0$ the least element of $B$. If $a b = a_0 b_0$ with $a \in A$, $b \in B$ and $(a, b) \neq (a_0, b_0)$, then $a \geq a_0$ and $b \geq b_0$ with one inequality strict, so strict monotonicity gives $a b > a_0 b_0$, a contradiction. The two maximal elements give the second pair. So $\mathbb{N}$, $\mathbb{Z}$, $\mathbb{Q}$ and $\mathbb{R}$ have unique sums.

The class is closed under the usual constructions. The instances `Prod.instUniqueProds` and `UniqueProds.instForall` treat products, `UniqueProds.instMulOpposite` treats the opposite, and `instUniqueSumsFinsupp` and `instTwoUniqueSumsDFinsupp` treat finitely supported functions. The instances `Additive.instUniqueSumsOfUniqueProds` and `Multiplicative.instUniqueProdsOfUniqueSums` move the property between the two type tags.

Three small modules add examples. The module `Mathlib.Algebra.Group.UniqueProds.VectorSpace` gives each vector space over $\mathbb{Q}$ two unique sums, by the instance `instTwoUniqueSumsOfModuleRat`. A basis gives an injective additive map into finitely supported functions with values in $\mathbb{Q}$, and `TwoUniqueSums.of_injective_addHom` transfers the property. The module `Mathlib.Algebra.FreeMonoid.UniqueProds` gives the free monoid two unique products, by `FreeMonoid.instTwoUniqueProds`. The module `Mathlib.Algebra.FreeAbelianGroup.UniqueSums` gives the free abelian group two unique sums, by `instTwoUniqueSumsFreeAddCommGroup`, through its description as finitely supported functions with values in $\mathbb{Z}$.

#### Affine monoids

The module `Mathlib.Algebra.AffineMonoid.Basic` defines `IsAffineMonoid M` for a commutative monoid $M$. It is a class abbreviation for the three conditions `IsCancelMul M`, `Monoid.FG M` and `HasUniqueRoots M`. The additive class is `IsAffineAddMonoid`. The instances such as `IsAffineMonoid.toIsMulFG` and `IsAffineMonoid.toHasUniqueRoots` extract the three conditions.

The module `Mathlib.Algebra.AffineMonoid.Embedding` embeds an affine additive monoid in a lattice. The number `AffineAddMonoid.dim M` is the rank `Module.finrank` over $\mathbb{Z}$ of the Grothendieck group `Algebra.GrothendieckAddGroup M`, the group of formal differences of $M$ (Chapter 13 constructs it as a localization of $M$). The map `AffineAddMonoid.embedding M` goes from $M$ to `FreeAddCommGroup (Fin (AffineAddMonoid.dim M))`, that is to $\mathbb{Z}^d$, and `AffineAddMonoid.embedding_injective` states that it is injective. The proof has three steps. Since $M$ is cancellative, the map from $M$ to its group of differences is injective. That group is finitely generated, since the generators of $M$ generate it, and it is torsion-free, since $M$ has unique division. A finitely generated torsion-free abelian group is free of finite rank, so a basis identifies it with $\mathbb{Z}^d$.

The module `Mathlib.Algebra.AffineMonoid.UniqueSums` combines the embedding with the results above. The instance `AffineAddMonoid.to_twoUniqueSums` pulls back the two unique sums of $\mathbb{Z}^d$ along the injective embedding. The multiplicative form is `AffineMonoid.to_twoUniqueProds`. Both instances have a low priority.

The module `Mathlib.Algebra.AffineMonoid.Irreducible` treats the irreducible elements of a commutative monoid with trivial units, in the sense of Chapter 1. The main result is `irreducible_subset_of_submonoidClosure_eq_top`: if a set $S$ generates $M$, then $S$ contains every irreducible element. The proof: let $p$ be irreducible. Since $S$ generates $M$, $p$ is a product $s_1 \cdots s_k$ of elements of $S$. The product is not $1$, so $k \geq 1$. An irreducible element is not a product of two non-units, so all factors except one are units, so they are $1$, and $p$ is the remaining factor $s_i \in S$. The form `irreducible_mem_submonoidClosure_subset` states the same for the irreducible elements of a closure.

Two consequences follow. With a finite generating set, `finite_irreducible` states that $M$ has only finitely many irreducible elements, and `Submonoid.FG.finite_irreducible_mem_submonoidClosure` states the same for a finitely generated submonoid. In a cancellative monoid of this kind, the irreducible elements generate, by `Submonoid.closure_irreducible`. Together the two results say that the irreducible elements form the unique minimal generating set of an affine monoid with trivial units.

#### Common errors

1. `IsMulTorsionFree` is the weak class. A lemma such as `pow_left_inj` for elements that do not commute needs `HasUniqueRoots`, and instance search does not find it from `IsMulTorsionFree` in a noncommutative group. Use `Commute.pow_left_inj` with a proof of commutation, or add the stronger hypothesis.
2. `UniqueMul A B a0 b0` does not say that $a_0 \in A$ or $b_0 \in B$. A statement such as `UniqueMul.iff_existsUnique` takes the two memberships as hypotheses. Keep them next to the predicate, as `UniqueProds.uniqueMul_of_nonempty` does.
3. The embedding `AffineAddMonoid.embedding` exists only in the additive form. It takes the three instances `AddCancelCommMonoid`, `AddMonoid.FG` and `HasUniqueDiv`. For a multiplicative monoid $M$, apply it to `Additive M`, as the proof of `AffineMonoid.to_twoUniqueProds` does.

### Exercises

1. (A) Let $n \geq 2$. Show that the additive group $\mathbb{Z}/n\mathbb{Z}$ is not torsion-free, and say which row of the table of identities fails for it.
2. (A) Let $A = \{a\}$ and let $B$ be a nonempty finite subset of a left cancellative semigroup. Show that `UniqueMul A B a b` holds for each $b \in B$.
3. (B) Let $G$ be a group with an element $g \neq 1$ of finite order, and let $H$ be the finite subgroup that $g$ generates. Take $A = B = H$ and show that each element of $A B$ has $|H| \geq 2$ expressions. Deduce that $G$ does not have unique products.
4. (B) Find the irreducible elements of the additive monoid $\mathbb{N}^2$. Use the additive form `addIrreducible_subset_of_addSubmonoidClosure_eq_top` to show that each generating set of $\mathbb{N}^2$ contains them.
5. (B) Let $M$ be the submonoid of $(\mathbb{N}, +)$ generated by $2$ and $3$. Show that $M$ is affine, that its irreducible elements are $2$ and $3$, and that its group of differences is $\mathbb{Z}$, so that its dimension is $1$.
6. (C) Let $K$ be the group with generators $a, b$ and the relation $b a b^{-1} = a^{-1}$. Show that $(a b)^2 = b^2$ and that $a b \neq b$, so $K$ does not have unique roots. Given that $1$ is the only element of finite order in $K$, show that $K$ is torsion-free in the sense of `IsMulTorsionFree`.

### Reference

<?reference?>
