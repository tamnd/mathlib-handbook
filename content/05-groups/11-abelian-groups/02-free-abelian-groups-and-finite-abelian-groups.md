---
title: Free abelian groups and finite abelian groups
kind: api
modules:
  - Mathlib.GroupTheory.FreeAbelianGroup
  - Mathlib.Algebra.FreeAbelianGroup.Finsupp
  - Mathlib.GroupTheory.FiniteAbelian.Basic
  - Mathlib.GroupTheory.FiniteAbelian.Duality
explains:
  E2: [FreeAddCommGroup.lift_apply_of, FreeAddCommGroup.lift_ext, FreeAddCommGroup.uniqueEquiv, CommGroup.finite_of_fg_isMulTorsion, CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity, CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity]
  E1: auto
families: []
requires: [V05.C04, V05.C05, V05.C10]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Free abelian groups and finite abelian groups

### Overview

The free abelian group on a set $X$ is the commutative group of formal sums $\sum_{x} n_x\, x$ with integer coefficients and only finitely many $n_x \ne 0$. Each map from $X$ to a commutative group extends to a unique homomorphism on it. The module `Mathlib.GroupTheory.FreeAbelianGroup` builds this group as `FreeAddCommGroup X`, with the multiplicative form `FreeCommGroup X`, and gives its universal property and its functoriality. Chapter 10 builds the free group, and the free commutative group is its abelianization.

The modules `Mathlib.GroupTheory.FiniteAbelian.Basic` and `Mathlib.GroupTheory.FiniteAbelian.Duality` give the structure of finitely generated commutative groups. Such a group is a product of a free part $\mathbb{Z}^n$ and of cyclic groups of prime power order. A finite commutative group is a product of cyclic groups, and its group of characters is isomorphic to it. The torsion subgroup and the free rank of the previous section are the two halves of the structure theorem.

### The library around it

#### The free abelian group

The type `FreeAddCommGroup α` is the free additive commutative group on a type $\alpha$, and `FreeCommGroup α` is the multiplicative form. The library defines `FreeCommGroup α` as `Group.Abelianization (FreeGroup α)`, the abelianization of the free group, and the additive form through `Additive`. The two forms are related by `FreeCommGroup.freeCommGroupEquivMultiplicative` and `FreeAddCommGroup.freeAddCommGroupEquivAdditive`. The map of the generators is `FreeAddCommGroup.of : α → FreeAddCommGroup α`. It is injective (`FreeAddCommGroup.of_injective`), so the free group on a nonempty type is nontrivial (`FreeAddCommGroup.instNontrivialOfNonempty`), and the free group on the empty type is trivial (`FreeAddCommGroup.instUniqueOfIsEmpty`).

The universal property is an equivalence. `FreeAddCommGroup.lift` is the equivalence `(α → β) ≃ (FreeAddCommGroup α →+ β)` for each additive commutative group $\beta$. In words: a map $f : \alpha \to \beta$ extends to the homomorphism $\sum n_x\, x \mapsto \sum n_x f(x)$, and each homomorphism comes from its values on the generators.

| Lean name | Statement |
|---|---|
| `FreeAddCommGroup.lift_apply_of` | $\operatorname{lift}(f)(\operatorname{of} x) = f(x)$ |
| `FreeAddCommGroup.lift_unique` | a homomorphism $g$ with $g(\operatorname{of} x) = f(x)$ for each $x$ is $\operatorname{lift}(f)$ |
| `FreeAddCommGroup.lift_ext` | two homomorphisms that agree on each $\operatorname{of} x$ are equal |
| `FreeAddCommGroup.lift_add` | $\operatorname{lift}(f + g) = \operatorname{lift}(f) + \operatorname{lift}(g)$ |
| `FreeAddCommGroup.lift_neg` | $\operatorname{lift}(-f) = -\operatorname{lift}(f)$ |
| `FreeAddCommGroup.liftAddEquiv` | $\operatorname{lift}$ as an isomorphism of additive groups |

The first line is the definition of the extension at a generator. The third line has a short proof: the set of elements where the two homomorphisms agree is a subgroup, and it contains the generators, so it is the whole group. The lemma `FreeAddCommGroup.lift_ext` is tagged for the tactic `ext`, so a proof of the equality of two homomorphisms out of a free abelian group reduces to their values on the generators. The multiplicative forms are `FreeCommGroup.lift`, `FreeCommGroup.lift_apply_of` and the others with the prefix `FreeCommGroup`.

The principle of induction is `FreeAddCommGroup.induction_on`. A property of all elements follows from four cases: $0$, a generator $\operatorname{of} x$, its negative $-\operatorname{of} x$, and a sum of two elements that have the property.

The construction is a functor. A map $f : \alpha \to \beta$ gives the homomorphism `FreeAddCommGroup.map f`, which sends $\operatorname{of} x$ to $\operatorname{of} f(x)$. It respects composition (`FreeAddCommGroup.map_comp`) and the identity (`FreeAddCommGroup.map_id`), and an equivalence of types gives an isomorphism of groups (`FreeAddCommGroup.equivOfEquiv`). The lemma `FreeAddCommGroup.lift_comp` says that $\operatorname{lift}(g \circ f) = \operatorname{lift}(g) \circ \operatorname{map}(f)$.

The free abelian group on one generator is $\mathbb{Z}$: `FreeAddCommGroup.uniqueEquiv` is an isomorphism `FreeAddCommGroup T ≃+ ℤ` for a type $T$ with exactly one element. Proof: the map $\operatorname{lift}(x \mapsto 1)$ goes to $\mathbb{Z}$, the map $n \mapsto n \cdot \operatorname{of}(t)$ goes back, and both composites are the identity by `FreeAddCommGroup.lift_ext` and by the uniqueness of homomorphisms out of $\mathbb{Z}$. For a general type, another module gives the isomorphism `FreeAddCommGroup.equivFinsupp` with the finitely supported functions $\alpha \to_0 \mathbb{Z}$, the formal sums of the first paragraph.

The module `Mathlib.Algebra.FreeAbelianGroup.Finsupp` holds this isomorphism. The homomorphism `FreeAddCommGroup.toFinsupp` sends an element to its function of coefficients, with `FreeAddCommGroup.toFinsupp_of` for a generator, and `Finsupp.toFreeAddCommGroup` goes back, with `Finsupp.toFreeAddCommGroup_single`: the function with value $n$ at $x$ and $0$ elsewhere goes to $n \cdot \operatorname{of}(x)$. The two maps make the equivalence `FreeAddCommGroup.equivFinsupp`. The coefficient of $x$ is the homomorphism `FreeAddCommGroup.coeff x` to $\mathbb{Z}$, and `FreeAddCommGroup.coeff_of` gives $1$ at $\operatorname{of} x$ and $0$ at the other generators. The support `FreeAddCommGroup.support` is the finite set of generators with a nonzero coefficient, by `FreeAddCommGroup.mem_support_iff`. It is empty only for $0$, by `FreeAddCommGroup.support_eq_empty`, and a nonzero integer multiple has the same support, by `FreeAddCommGroup.support_zsmul`, because $\mathbb{Z}$ has no zero divisors.

#### The structure of finitely generated commutative groups

The main theorem of `Mathlib.GroupTheory.FiniteAbelian.Basic` is the structure theorem. Let $G$ be a finitely generated additive commutative group. Then there are $n \in \mathbb{N}$, a finite family of primes $p_i$ and exponents $e_i$ such that

$$G \cong \mathbb{Z}^n \times \bigoplus_{i} \mathbb{Z}/p_i^{e_i}\mathbb{Z}.$$

This is `AddCommGroup.equiv_free_prod_directSum_zmod`. The statement is an existence statement: it gives `Nonempty (G ≃+ (Fin n →₀ ℤ) × ⨁ i, ZMod (p i ^ e i))`, and the isomorphism is a choice. The proof views $G$ as a finitely generated module over $\mathbb{Z}$ and applies the structure theorem for finitely generated modules over a principal ideal domain. The multiplicative form is `CommGroup.equiv_free_prod_prod_multiplicative_zmod`, with products of `Multiplicative ℤ` and `Multiplicative (ZMod (p i ^ e i))`.

For a finite group the free part is trivial, because $\mathbb{Z}^n$ is infinite for $n > 0$.

| Lean name | Statement |
|---|---|
| `AddCommGroup.equiv_directSum_zmod_of_finite` | a finite $G$ is $\bigoplus_i \mathbb{Z}/p_i^{e_i}\mathbb{Z}$ with primes $p_i$ |
| `AddCommGroup.equiv_directSum_zmod_of_finite'` | a finite $G$ is $\bigoplus_i \mathbb{Z}/n_i\mathbb{Z}$ with each $n_i > 1$ |
| `CommGroup.equiv_prod_multiplicative_zmod_of_finite` | the multiplicative form of the second line |

The theorem has a corollary about torsion. A finitely generated commutative torsion group is finite, by `CommGroup.finite_of_fg_isMulTorsion` and the additive form `AddCommGroup.finite_of_fg_isAddTorsion`. Proof from the structure theorem: a factor $\mathbb{Z}$ has elements of infinite order, so a torsion group has $n = 0$, and the remaining product is finite. The module form is `Module.finite_of_fg_torsion` for a finite torsion $\mathbb{Z}$-module. The lemma `Subgroup.finiteIndex_range_powMonoidHom_of_fg` says that the subgroup $G^n = \{g^n\}$ has finite index in a finitely generated commutative group $G$ for $n \ne 0$. This is the hypothesis of `CommGroup.fg_of_descent` in Chapter 4.

#### Duality of finite commutative groups

Let $G$ be a finite commutative group and let $M$ be a commutative monoid. A *character* of $G$ with values in $M$ is a homomorphism $G \to M^\times$, and the characters form the commutative group `G →* Mˣ`. The module `Mathlib.GroupTheory.FiniteAbelian.Duality` assumes `HasEnoughRootsOfUnity M (Monoid.exponent G)`: the group of $e$-th roots of unity in $M$ is cyclic of order $e$, where $e$ is the exponent of $G$. The complex numbers satisfy this for each $e \ge 1$, and so does a finite field whose order is $1$ modulo $e$.

The first result says that characters separate points. `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`: if $a \ne 1$, then there is a character $\varphi$ with $\varphi(a) \ne 1$. Proof sketch: by the structure theorem, $G$ is a product of cyclic groups $\mathbb{Z}/n_i$, each $n_i$ divides $e$, and some coordinate $a_i$ of $a$ is not $0$. A primitive $n_i$-th root of unity $\zeta$ exists in $M$ by the hypothesis, and $x \mapsto \zeta^{x_i}$ is a character that is not $1$ at $a$. The consequence `CommGroup.forall_apply_eq_apply_iff` says that $g = g'$ if and only if $\varphi(g) = \varphi(g')$ for each character $\varphi$.

The second result says that $G$ and its character group have the same order, and in fact they are isomorphic.

| Lean name | Statement |
|---|---|
| `CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity` | $\lvert \operatorname{Hom}(G, M^\times) \rvert = \lvert G \rvert$ |
| `CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity` | there is an isomorphism $\operatorname{Hom}(G, M^\times) \cong G$ |
| `CommGroup.monoidHomMonoidHomEquiv` | the evaluation map identifies $G$ with its double dual |
| `CommGroup.subgroupOrderIsoSubgroupMonoidHom` | $H \mapsto H^\perp$ is an order-reversing bijection of the subgroups of $G$ and of its character group |
| `CommGroup.forall_monoidHom_apply_eq_one_iff` | $x \in H$ if and only if each character that is $1$ on $H$ is $1$ at $x$ |
| `MonoidHom.domRestrict_surjective` | each character of a subgroup $H$ extends to $G$ |

The count has a short proof from the structure theorem. The characters of a product are the products of the characters of the factors. A character of $\mathbb{Z}/n$ is fixed by the image of $1$, which is an $n$-th root of unity, and there are exactly $n$ of them in $M$ because $n$ divides $e$. So the character group of $\prod_i \mathbb{Z}/n_i$ has $\prod_i n_i$ elements. The isomorphism with $G$ is not canonical: it depends on a choice of generators of the factors, and for this reason the library states only that an isomorphism exists. The double dual isomorphism `CommGroup.monoidHomMonoidHomEquiv` is canonical: it sends $g$ to the evaluation $\varphi \mapsto \varphi(g)$, and it is injective by the separation of points and bijective by the count. The extension of characters from a subgroup follows by a count too: `CommGroup.card_domRestrictHom_ker` says that the kernel of the restriction map to $H$ has the order of $G / H$.

#### Common errors

1. The old name of the free abelian group is deprecated. Use `FreeAddCommGroup` and `FreeCommGroup`, and for the group ring of a type use `MonoidAlgebra ℤ` and not a ring structure on the free abelian group.
2. The structure theorems give a proof that an isomorphism exists, not an isomorphism. In a proof, use `obtain` to get the isomorphism. In a definition, the isomorphism comes from the axiom of choice, and no lemma describes the chosen map.
3. The duality results need the instance `HasEnoughRootsOfUnity M (Monoid.exponent G)` for the exponent of $G$, not for its order. Lean does not find it from a hypothesis on the order.

### Exercises

1. (A) Use `FreeAddCommGroup.lift_ext` to prove that `FreeAddCommGroup.map id` is the identity homomorphism.
2. (A) Use `CommGroup.finite_of_fg_isMulTorsion` to prove that a finitely generated commutative group of exponent $n$ is finite.
3. (B) Prove that `FreeAddCommGroup (Fin 2)` is not isomorphic to $\mathbb{Z}$. Consider the quotient by twice the group.
4. (B) List the commutative groups of order $72$ up to isomorphism with `AddCommGroup.equiv_directSum_zmod_of_finite`.
5. (B) Let $G$ be a finite commutative group. Prove that the number of elements of order dividing $2$ in $G$ equals the number of characters $G \to \mathbb{C}^\times$ with values in $\{\pm 1\}$.
6. (C) Let $H$ be a subgroup of a finite commutative group $G$. Prove with `CommGroup.subgroupOrderIsoSubgroupMonoidHom` that $G$ has a subgroup isomorphic to $G / H$.

### Reference

<?reference?>
