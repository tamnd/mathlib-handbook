---
title: Group-like and primitive elements and monoid algebras
kind: api
modules:
  - Mathlib.RingTheory.Coalgebra.GroupLike
  - Mathlib.RingTheory.Bialgebra.GroupLike
  - Mathlib.RingTheory.HopfAlgebra.GroupLike
  - Mathlib.RingTheory.Coalgebra.Primitive
  - Mathlib.RingTheory.Bialgebra.Primitive
  - Mathlib.RingTheory.HopfAlgebra.Primitive
  - Mathlib.RingTheory.Coalgebra.MonoidAlgebra
  - Mathlib.RingTheory.Bialgebra.MonoidAlgebra
  - Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
explains:
  E2: [IsGroupLikeElem.mul, IsGroupLikeElem.antipode_mul_cancel, linearIndepOn_isGroupLikeElem, Coalgebra.counit_eq_zero_of_comul_eq_tmul_add_tmul, Bialgebra.IsPrimitiveElem.commutator, Bialgebra.IsPrimitiveElem.antipode_eq_neg, MonoidAlgebra.isGroupLikeElem_iff_mem_range_of, MonoidAlgebra.mapDomainBialgHomEquiv]
  E1: auto
families: []
requires: [V08.C02, V05.C01, V06.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Group-like and primitive elements and monoid algebras

### Overview

Two kinds of elements of a coalgebra have a simple comultiplication. An element $g$ is *group-like* if $\Delta g = g \otimes g$ and $\varepsilon(g) = 1$. An element $a$ is *primitive* if $\Delta a = 1 \otimes a + a \otimes 1$, and then $\varepsilon(a) = 0$. In a bialgebra, the group-like elements form a monoid and the primitive elements form a Lie algebra under the commutator. In a Hopf algebra, the group-like elements form a group with the antipode as inverse, and the antipode of a primitive element is its negative.

The monoid algebra $R[M]$ is the main example. Each element $m$ of $M$ is group-like, the group-like elements span $R[M]$, and over a domain they are exactly the elements of $M$. So a bialgebra map $R[G] \to R[H]$ between group algebras over a domain is the same as a group homomorphism $G \to H$. This section uses the bialgebras and Hopf algebras of Sections 2 and 3. The monoid algebra $R[M]$ is the free module on $M$, with the product that extends the product of $M$.

### The library around it

#### Group-like elements

The predicate `IsGroupLikeElem R a` has the two fields `IsGroupLikeElem.counit_eq_one` and `IsGroupLikeElem.comul_eq_tmul_self`, and `isGroupLikeElem_iff` unfolds it. The subtype is the structure `GroupLike R A`, with the field `GroupLike.val` and the equivalence `GroupLike.valEquiv` with `Subtype (IsGroupLikeElem R)`. The basic facts for a coalgebra are:

| Lean name | Statement |
| --- | --- |
| `isGroupLikeElem_self` | an element $r$ of the coalgebra $R$ is group-like if and only if $r = 1$ |
| `IsGroupLikeElem.ne_zero` | over a nontrivial ring, a group-like element is not $0$ |
| `IsGroupLikeElem.map` | a coalgebra map sends group-like elements to group-like elements |
| `isGroupLikeElem_map_equiv` | a coalgebra equivalence preserves and reflects the property |
| `linearIndepOn_isGroupLikeElem` | over a domain, the group-like elements are linearly independent |

The last result is the main theorem on group-like elements, and `linearIndep_groupLikeVal` states it for the family `GroupLike.val`. The library proves it over a domain $R$ for a torsion-free module $A$. Over a field the proof is short. Suppose that the result is false, and take a group-like $g$ and a linearly independent family of group-like elements $g_1, \dots, g_n$ different from $g$ with $g = \sum_i c_i g_i$. Then
$$\sum_{i, j} c_i c_j\, g_i \otimes g_j = g \otimes g = \Delta g = \sum_i c_i\, g_i \otimes g_i.$$
The tensors $g_i \otimes g_j$ are linearly independent, so $c_i c_j = 0$ for $i \neq j$ and $c_i^2 = c_i$. So at most one $c_i$ is not zero, and it equals $1$. Then $g = g_i$, which is false, or $g = 0$, which contradicts $\varepsilon(g) = 1$. In particular, a coalgebra of dimension $n$ over a field has at most $n$ group-like elements.

#### Group-like elements in bialgebras and Hopf algebras

In a bialgebra, $1$ is group-like (`IsGroupLikeElem.one`), and the product of two group-like elements is group-like (`IsGroupLikeElem.mul`). Proof: the comultiplication and the counit are multiplicative, so
$$\Delta(gh) = \Delta(g)\Delta(h) = (g \otimes g)(h \otimes h) = gh \otimes gh, \qquad \varepsilon(gh) = \varepsilon(g)\varepsilon(h) = 1.$$
Powers are group-like by `IsGroupLikeElem.pow`. The submonoid of group-like elements is `groupLikeSubmonoid R A`, and the structure `GroupLike R A` is a monoid (`GroupLike.instMonoid`) with the inclusion `GroupLike.valMonoidHom`. It is commutative when $A$ is commutative (`GroupLike.instCommMonoid`). A two-sided inverse of a group-like element is group-like (`IsGroupLikeElem.of_mul_eq_one`), and for units, `isGroupLikeElem_unitsInv` says that $u^{-1}$ is group-like if and only if $u$ is.

In a Hopf algebra every group-like element is a unit, with the antipode as inverse. Apply the antipode axiom to $g$: since $\Delta g = g \otimes g$,
$$S(g)\, g = \varepsilon(g) \cdot 1 = 1, \qquad g\, S(g) = 1.$$
These are `IsGroupLikeElem.antipode_mul_cancel` and `IsGroupLikeElem.mul_antipode_cancel`, and `IsGroupLikeElem.isUnit` follows. The element $S(g)$ is group-like (`IsGroupLikeElem.antipode`), and $S(S(g)) = g$ (`IsGroupLikeElem.antipode_antipode`) because inverses are unique. So `GroupLike R A` is a group, `GroupLike.instGroup`, with the inverse $S$ (`GroupLike.val_inv`), and `GroupLike.toUnits` maps it to the units of $A$. The group is commutative for a commutative $A$ (`GroupLike.instCommGroup`).

#### Skew-primitive and primitive elements

Let $g$ and $h$ be elements of a coalgebra. An element $a$ is *$(g, h)$-skew-primitive* if $\varepsilon(a) = 0$ and $\Delta a = g \otimes a + a \otimes h$. The predicate is `Coalgebra.IsSkewPrimitiveElem R g h a`, and these elements form a submodule `Coalgebra.skewPrimitive R g h` with the closure lemmas `Coalgebra.IsSkewPrimitiveElem.add`, `Coalgebra.IsSkewPrimitiveElem.smul`, `Coalgebra.IsSkewPrimitiveElem.neg` and `Coalgebra.IsSkewPrimitiveElem.zero`. Coalgebra maps preserve them (`Coalgebra.IsSkewPrimitiveElem.map`, `Coalgebra.isSkewPrimitiveElem_map_equiv`).

The condition on the counit is redundant when $g$ and $h$ have counit $1$: this is `Coalgebra.counit_eq_zero_of_comul_eq_tmul_add_tmul`, and `Coalgebra.isSkewPrimitiveElem_iff_comul_eq_tmul_add_tmul` is the resulting criterion. Proof: apply $\varepsilon \otimes \mathrm{id}$ to $\Delta a = g \otimes a + a \otimes h$ and identify $R \otimes A$ with $A$. The counit axiom gives $a = \varepsilon(g)\, a + \varepsilon(a)\, h = a + \varepsilon(a)\, h$, so $\varepsilon(a)\, h = 0$ by cancellation. Apply $\varepsilon$: $\varepsilon(a) = \varepsilon(a)\varepsilon(h) = 0$. The lemma needs `IsCancelAdd A` for the cancellation.

In a bialgebra, `Bialgebra.IsPrimitiveElem R a` is the case $g = h = 1$, as an abbreviation. The criterion `Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul` says that $a$ is primitive if and only if $\Delta a = 1 \otimes a + a \otimes 1$, and `Bialgebra.counit_eq_zero_of_comul_eq_tmul_add_tmul` is the counit statement. Over a nontrivial ring, $1$ is not primitive (`Bialgebra.IsPrimitiveElem.ne_one`), since $\varepsilon(1) = 1$.

The commutator $[a, b] = ab - ba$ of two primitive elements is primitive (`Bialgebra.IsPrimitiveElem.commutator`). Proof: $\Delta$ is multiplicative, so
$$\Delta(ab) = (1 \otimes a + a \otimes 1)(1 \otimes b + b \otimes 1) = 1 \otimes ab + b \otimes a + a \otimes b + ab \otimes 1.$$
The formula for $\Delta(ba)$ has the same two middle terms, so $\Delta(ab - ba) = 1 \otimes (ab - ba) + (ab - ba) \otimes 1$. So the primitive elements form a Lie subalgebra of $A$ for the commutator. In the symmetric algebra of Section 2, each $\iota x$ is primitive.

In a Hopf algebra, the antipode axiom for a primitive $a$ gives $S(1)\, a + S(a) \cdot 1 = \varepsilon(a) \cdot 1 = 0$. Since $S(1) = 1$, this is $S(a) = -a$, the lemma `Bialgebra.IsPrimitiveElem.antipode_eq_neg`. Then $S(a)$ is primitive (`Bialgebra.IsPrimitiveElem.antipode`) and $S(S(a)) = a$ (`Bialgebra.IsPrimitiveElem.antipode_antipode`).

#### The coalgebra of a monoid algebra

For a coalgebra $A$ and any type $X$, the monoid algebra `MonoidAlgebra A X` is a coalgebra (`MonoidAlgebra.instCoalgebra`). It is a direct sum of copies of $A$, one for each $x$, as in the coalgebra of finitely supported functions of Section 1. On a single term
$$\Delta(\mathrm{single}\ x\ a) = (\mathrm{single}\ x \otimes \mathrm{single}\ x)(\Delta a), \qquad \varepsilon(\mathrm{single}\ x\ a) = \varepsilon(a),$$
the lemmas `MonoidAlgebra.comul_single` and `MonoidAlgebra.counit_single`. For $A = R$ this is $\Delta(x) = x \otimes x$ and $\varepsilon(x) = 1$. The coalgebra is cocommutative when $A$ is (`MonoidAlgebra.instIsCocomm`). The additive version is `AddMonoidAlgebra.instCoalgebra`, and the Laurent polynomials $R[T, T^{-1}] = R[\mathbb{Z}]$ have `LaurentPolynomial.instCoalgebra` with `LaurentPolynomial.comul_C_mul_T`, `LaurentPolynomial.comul_C` and `LaurentPolynomial.counit_C_mul_T`.

#### The bialgebra of a monoid algebra

For a monoid $M$, `MonoidAlgebra.instBialgebra` makes $A[M]$ a bialgebra, and `LaurentPolynomial.instBialgebra` makes $R[T, T^{-1}]$ one, with $\Delta(T^n) = T^n \otimes T^n$ and $\varepsilon(T^n) = 1$ (`LaurentPolynomial.comul_T`, `LaurentPolynomial.counit_T`). Every element of $M$ is group-like (`MonoidAlgebra.isGroupLikeElem_of`, `MonoidAlgebra.isGroupLikeElem_single_one`), and the group-like elements span the algebra (`MonoidAlgebra.span_isGroupLikeElem`).

Over a domain, the group-like elements of $R[M]$ are exactly the elements of $M$: this is `MonoidAlgebra.isGroupLikeElem_iff_mem_range_of`, with the variant `MonoidAlgebra.isGroupLikeElem_iff_mem_range_single_one`. Proof: let $x = \sum_m c_m m$ be group-like. Then
$$\sum_{m, n} c_m c_n\, m \otimes n = x \otimes x = \Delta x = \sum_m c_m\, m \otimes m.$$
The tensors $m \otimes n$ form a basis of $R[M] \otimes R[M]$, so $c_m c_n = 0$ for $m \neq n$ and $c_m^2 = c_m$. Over a domain, each $c_m$ is $0$ or $1$, and at most one $c_m$ is $1$. Since $\varepsilon(x) = \sum_m c_m = 1$, exactly one $c_m$ is $1$, and $x = m$.

The bialgebra maps of monoid algebras follow the monoid maps:

| Lean name | Meaning |
| --- | --- |
| `MonoidAlgebra.mapDomainBialgHom` | a monoid map $M \to N$ gives a bialgebra map $R[M] \to R[N]$ |
| `MonoidAlgebra.bialgHom_ext` | a bialgebra map out of $A[M]$ is fixed by its values on $M$ and on $A$ |
| `MonoidAlgebra.domCongrBialgEquiv` | a monoid isomorphism gives a bialgebra equivalence |
| `MonoidAlgebra.bialgEquivOfSubsingleton` | $R[M] \simeq R$ for a trivial monoid $M$ |
| `MonoidAlgebra.liftGroupLikeBialgHom` | the bialgebra map $R[\mathrm{GroupLike}(A)] \to A$ |
| `MonoidAlgebra.toAdditiveBialgEquiv` | $A[M] \simeq A[\mathrm{Additive}\ M]$ |

By `linearIndepOn_isGroupLikeElem`, the map `MonoidAlgebra.liftGroupLikeBialgHom` is injective over a field: its image is the span of the group-like elements of $A$.

For groups $G$ and $H$ over a domain, a bialgebra map $f : R[G] \to R[H]$ sends each $g$ to a group-like element, which is an element of $H$. So $f$ restricts to a group homomorphism `MonoidAlgebra.mapDomainOfBialgHom f`, and `MonoidAlgebra.mapDomainBialgHomEquiv` is the bijection
$$(G \to^{*} H) \simeq (R[G] \to_{ac} R[H]).$$
For commutative groups $G$ and $H$, `MonoidAlgebra.mapDomainBialgHomMulEquiv` makes it a group isomorphism for the convolution product. The additive form is `AddMonoidAlgebra.mapDomainBialgHomAddEquiv`. In the same spirit, `MonoidAlgebra.liftMulEquiv` identifies the monoid maps $M \to A$ to a commutative algebra $A$ with the algebra maps $R[M] \to A$ under convolution. The lemmas `MonoidAlgebra.convMul_algHom_single_one` and `MonoidAlgebra.convMul_bialgHom_single_one` say that the convolution of two maps multiplies their values at each $m$, since $\Delta m = m \otimes m$.

#### The Hopf algebra of a group algebra

For a group $G$ and a Hopf algebra $A$, `MonoidAlgebra.instHopfAlgebra` makes $A[G]$ a Hopf algebra, with
$$S(\mathrm{single}\ g\ a) = \mathrm{single}\ g^{-1}\ (S a),$$
the lemma `MonoidAlgebra.antipode_single`. For $A = R$ this is $S(g) = g^{-1}$, which agrees with the inverse of the group of group-like elements. The additive version is `AddMonoidAlgebra.instHopfAlgebra` with `AddMonoidAlgebra.antipode_single`. The Laurent polynomials form a Hopf algebra (`LaurentPolynomial.instHopfAlgebra`) with $S(T^n) = T^{-n}$ (`LaurentPolynomial.antipode_T`, `LaurentPolynomial.antipode_C_mul_T`). This is the Hopf algebra of the multiplicative group: by `MonoidAlgebra.liftMulEquiv`, an algebra map $R[T, T^{-1}] \to C$ is a unit of $C$, and convolution is the product of units.

#### Common errors

1. A learner proves that a group-like element is not zero over any ring. The result `IsGroupLikeElem.ne_zero` needs a nontrivial ring: over the zero ring, $0 = 1$ is group-like.
2. A learner applies `MonoidAlgebra.isGroupLikeElem_iff_mem_range_of` over $\mathbb{Z}/6$. The proof needs a domain: in $\mathbb{Z}/6$, the element $3 g + 4 h$ is group-like for $g \neq h$, because $3 \cdot 4 = 0$, $3^2 = 3$, $4^2 = 4$ and $3 + 4 = 1$.
3. A learner looks for a structure of primitive elements under the name `Bialgebra.IsPrimitiveElem` and expects a submodule. It is a predicate, an abbreviation of `Coalgebra.IsSkewPrimitiveElem R 1 1`. The submodule is `Coalgebra.skewPrimitive R 1 1`.

### Exercises

1. (A) Prove that a coalgebra map sends a $(g, h)$-skew-primitive element to an $(f g, f h)$-skew-primitive element, as `Coalgebra.IsSkewPrimitiveElem.map` states.
2. (A) Compute $S(3 T^2 - T^{-1} + 5)$ in $\mathbb{Q}[T, T^{-1}]$ with `LaurentPolynomial.antipode_T`.
3. (B) Prove that if $g$ and $h$ are group-like in a coalgebra, then $g - h$ is $(g, h)$-skew-primitive.
4. (B) Show that the group-like elements of the coalgebra $R^{(\iota)}$ of Section 1 over a domain are the basis vectors $e_i$, and use `linearIndepOn_isGroupLikeElem` to bound their number in a coalgebra of dimension $n$ over a field.
5. (B) Let $A$ be a commutative algebra. Use `MonoidAlgebra.liftMulEquiv` to identify the algebra maps $R[\mathbb{Z}] \to A$ with the units of $A$, and show that convolution corresponds to the product of units.
6. (C) Over a field of characteristic $p$, prove that $a^p$ is primitive for a primitive element $a$ of a commutative bialgebra. Find where the proof uses that $p$ divides $\binom{p}{k}$ for $0 < k < p$.

### Reference

<?reference?>
