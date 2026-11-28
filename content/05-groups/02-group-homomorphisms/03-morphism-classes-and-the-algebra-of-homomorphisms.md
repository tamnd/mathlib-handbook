---
title: Morphism classes and the algebra of homomorphisms
kind: api
modules:
  - Mathlib.Algebra.Group.FunLike
  - Mathlib.Algebra.Group.IsApply
  - Mathlib.Algebra.Group.PowIterate
  - Mathlib.Algebra.Group.Hom.Basic
  - Mathlib.Algebra.Group.Hom.Instances
  - Mathlib.Algebra.Group.Hom.End
  - Mathlib.Algebra.Group.Hom.CompTypeclasses
  - Mathlib.Algebra.Group.Embedding
  - Mathlib.Algebra.Group.Equiv.Basic
  - Mathlib.Algebra.Group.Equiv.Finite
  - Mathlib.Algebra.Group.Graph
explains:
  E2: [FunLike.coe_mul, MonoidHom.instCommGroup, injective_iff_map_eq_one, MonoidHom.ofMapDiv, powMonoidHom, MonoidHom.flip, MonoidHom.eval, MulEquiv.monoidHomCongrLeft, MonoidHom.mem_graph, Subgroup.exists_eq_graph]
  E1: auto
families: []
requires: [V01.C03, V01.C04, V05.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Morphism classes and the algebra of homomorphisms

### Overview

Section 1 of this chapter defines the homomorphisms $M \to N$ of monoids and groups as functions that respect the operations. This section treats the homomorphisms as objects in their own right. When $N$ is commutative, the pointwise product of two homomorphisms is again a homomorphism, so the type `M →* N` is itself a commutative monoid, and a commutative group when $N$ is a group. The section also describes the classes that give a type of bundled maps its operations by evaluation, the criteria that build a homomorphism from less data, the isomorphisms between types of homomorphisms, and the graph of a homomorphism.

The modules are small and technical, but they appear in many proofs. A reader who meets `f * g` for two homomorphisms, `f ^ n` for an endomorphism, or the ring `AddMonoid.End M` of an abelian group, uses them. The section needs the functions and equivalences of Volume 1, the classes of Chapter 1 and the homomorphisms of Section 1.

### The library around it

#### Operations that are defined by evaluation

Many types of bundled maps carry an operation that is defined pointwise. The module `Mathlib.Algebra.Group.IsApply` gives a class for each such fact. For a type $F$ with a coercion to functions $\alpha \to \beta$ and a product on both $F$ and $\beta$, the class `IsMulApply F` states $(f g)(x) = f(x) g(x)$. The classes `IsOneApply`, `IsInvApply`, `IsDivApply`, `IsPowApply`, `IsSMulApply`, `IsNatCastApply` and `IsIntCastApply` state the same for the other operations, and the additive forms such as `IsZeroApply` and `IsNegApply` follow the usual naming. For endomorphisms the product is often the composite and not the pointwise product. The classes `IsMulApplyEqComp` and `IsOneApplyEqSelf` state $(f g)(x) = f(g(x))$ and $1(x) = x$.

From the classes the module derives the lemmas on the coercion. The lemma `FunLike.coe_mul` states that the underlying function of $f g$ is the pointwise product of the underlying functions of $f$ and $g$, and `FunLike.coe_one`, `FunLike.coe_inv`, `FunLike.coe_div` and `FunLike.coe_pow` are the companions. For composition, `FunLike.coe_mul_eq_comp` states that the underlying function of $f g$ is $f \circ g$, and `FunLike.coe_one_eq_id` states that the underlying function of $1$ is the identity. The module `Mathlib.Algebra.Group.PowIterate` adds the class `IsNPowApplyEqIterate` and the lemma `FunLike.coe_pow_eq_iterate`: the power $f^n$ of an endomorphism is the $n$-th iterate of $f$. An instance derives this class from the two classes for composition.

**Theorem (Transfer of the structure by evaluation).** Let $F$ be a type of maps $\alpha \to \beta$ whose coercion to functions is injective. If the operations of $F$ are pointwise and $\beta$ is a monoid, then $F$ is a monoid with the same operations.

*Proof.* The coercion is injective and it sends each operation of $F$ to the pointwise operation on $\alpha \to \beta$. The functions $\alpha \to \beta$ form a monoid. So each axiom holds in $F$, because it holds for the images. $\square$

The module `Mathlib.Algebra.Group.FunLike` gives these structures as definitions: `FunLike.monoid`, `FunLike.commMonoid`, `FunLike.group`, `FunLike.commGroup`, the cancellative forms such as `FunLike.cancelCommMonoid`, and the division monoids. They are definitions and not instances, because a type of maps can have more than one natural product. The definition `FunLike.compMonoid` builds the monoid of endomorphisms in which the product is the composite. The bundled form of the coercion is `FunLike.coeMonoidHom`, a homomorphism from $F$ to the functions $\alpha \to \beta$, and `FunLike.coeMonoidHom_injective` states that it is injective.

#### The pointwise operations on homomorphisms

**Theorem (Homomorphisms into a commutative monoid).** Let $M$ be a monoid and $N$ a commutative monoid. For homomorphisms $f, g : M \to N$, the map $x \mapsto f(x) g(x)$ is a homomorphism. With this product, the homomorphisms $M \to N$ form a commutative monoid. If $N$ is a commutative group, they form a commutative group, with inverse $x \mapsto f(x)^{-1}$.

*Proof.* For $x, y \in M$, $f(xy) g(xy) = f(x) f(y) g(x) g(y) = f(x) g(x) \cdot f(y) g(y)$, where the second step uses the commutativity of $N$. The map sends $1$ to $1 \cdot 1 = 1$. The axioms hold pointwise. For the inverse, $f(xy)^{-1} = (f(x) f(y))^{-1} = f(x)^{-1} f(y)^{-1}$, again by commutativity. $\square$

The instances are `MonoidHom.instCommMonoid` and `MonoidHom.instCommGroup`, in the module `Mathlib.Algebra.Group.Hom.Instances`. The operations live in `Mathlib.Algebra.Group.Hom.Basic`: the product is the instance `MonoidHom.mul`, with the evaluation lemma `MonoidHom.mul_apply`, and the inverse and division have `MonoidHom.inv_apply` and `MonoidHom.div_apply`. The powers have `MonoidHom.pow_apply` and `MonoidHom.zpow_apply`. The commutativity of $N$ is necessary. In a nonabelian group the pointwise product of two homomorphisms is in general not a homomorphism. The maps that only respect the identity, the type `OneHom M N`, need no commutativity, and they form a monoid by `OneHom.instMonoid` and a group by `OneHom.instGroup`.

Composition interacts with the pointwise product in a fixed way. On the right, composition is always additive: `MonoidHom.mul_comp` states $(g_1 g_2) \circ f = (g_1 \circ f)(g_2 \circ f)$. On the left it needs a homomorphism: `MonoidHom.comp_mul` states $g \circ (f_1 f_2) = (g \circ f_1)(g \circ f_2)$. The lemmas `MonoidHom.comp_inv`, `MonoidHom.inv_comp`, `MonoidHom.comp_div` and `MonoidHom.div_comp` complete the list. The additive forms give the abelian group `M →+ N`, which is the starting point of linear algebra over $\mathbb{Z}$.

In a commutative monoid, the power map is a homomorphism, because $(xy)^n = x^n y^n$. The bundled form is `powMonoidHom n`, with `powMonoidHom_apply`. In a commutative division monoid, `invMonoidHom` is the inverse map and `zpowGroupHom n` is the integer power. The lemma `invMonoidHom_comp_invMonoidHom` states that the inverse map composed with itself is the identity.

#### Homomorphisms of two variables

Since `N →* P` is a commutative monoid when $P$ is commutative, a homomorphism $M \to (N \to P)$ is a map of two variables that is a homomorphism in each variable. The module `Mathlib.Algebra.Group.Hom.Instances` gives the operations on such maps:

| Lean name | Statement |
|---|---|
| `MonoidHom.flip` | from $f : M \to (N \to P)$ to $N \to (M \to P)$, with $(\operatorname{flip} f)(y)(x) = f(x)(y)$ |
| `MonoidHom.eval` | $M \to ((M \to N) \to N)$, with $\operatorname{eval}(y)(x) = x(y)$ |
| `MonoidHom.compHom` | composition with $g : N \to P$ as a homomorphism of the hom monoids |
| `MonoidHom.compl₂` | precomposition in the second variable |
| `MonoidHom.compr₂` | postcomposition with $g : P \to Q$ |
| `MonoidHom.map_mul₂` | $f(m_1 m_2)(n) = f(m_1)(n) f(m_2)(n)$ |

The lemma `MonoidHom.ext_iff₂` reduces the equality of two such maps to the equality of all values $f(x)(y)$. The map `MonoidHom.eval` sends an element to evaluation at it. For an abelian group $G$, this is the map from $G$ to the homomorphisms out of its group of characters, the first step towards duality.

The module `Mathlib.Algebra.Group.Hom.End` treats the endomorphisms of an additive commutative monoid. The type `AddMonoid.End M` has the composite as product and the pointwise sum as sum, and the instances `AddMonoid.End.instSemiring` and `AddMonoid.End.instRing` make it a semiring, and a ring when $M$ is an abelian group. This is the endomorphism ring of an abelian group.

#### Building a homomorphism from less data

**Theorem (Test with the identity).** A homomorphism $f$ of a group $G$ into a monoid is injective if and only if $f(a) = 1$ implies $a = 1$.

*Proof.* An injective map sends only $1$ to $f(1) = 1$. Conversely, let $f(a) = f(b)$. Then $f(a b^{-1}) = f(a) f(b)^{-1} = 1$, so $a b^{-1} = 1$ and $a = b$. $\square$

The lemma is `injective_iff_map_eq_one`, and `injective_iff_map_eq_one'` gives the form with an equivalence. In the language of Chapter 3, a homomorphism is injective if and only if its kernel is trivial.

For groups, a map that respects division is already a homomorphism. The constructor `MonoidHom.ofMapDiv` takes $f : G \to H$ and a proof of $f(x / y) = f(x) / f(y)$ for all $x, y$. *Proof sketch.* With $x = y$ this gives $f(1) = 1$. With $x = 1$ it gives $f(y^{-1}) = f(y)^{-1}$. Then $f(xy) = f(x / y^{-1}) = f(x) / f(y)^{-1} = f(x) f(y)$. $\square$ The variant `MonoidHom.ofMapMulInv` takes the condition $f(a b^{-1}) = f(a) f(b)^{-1}$. The lemmas `MonoidHom.coe_of_map_div` and `MonoidHom.coe_of_map_mul_inv` state that the underlying function is $f$. A homomorphism can also transfer commutativity: `MonoidHom.commGroupOfInjective` makes $G$ commutative when it embeds into a commutative group, and `MonoidHom.commGroupOfSurjective` makes the image of a commutative group commutative.

#### Translations and the classes for composites

The module `Mathlib.Algebra.Group.Embedding` gives the translations as embeddings. In a left cancellative magma, `mulLeftEmbedding g` is the injective map $h \mapsto g h$, bundled as a `Function.Embedding`. The right form is `mulRightEmbedding`, and `mulLeftEmbedding_eq_mulRightEmbedding` states that the two agree in a commutative cancellative magma. In a group the translations are bijections, and a later section of this chapter packs them as permutations.

The module `Mathlib.Algebra.Group.Hom.CompTypeclasses` gives the class `MonoidHom.CompTriple`. An instance of `MonoidHom.CompTriple φ ψ χ` records that the composite $\psi \circ \varphi$ is $\chi$, by `MonoidHom.CompTriple.comp_eq`. The class `MonoidHom.CompTriple.IsId` marks a homomorphism that is the identity. Instance search then finds the composite of twisted maps without a rewrite. These classes serve the equivariant maps of Chapter 6, in which a map is twisted by a homomorphism of the acting monoids.

#### Isomorphisms of types of homomorphisms

**Theorem (Transport along isomorphisms).** An isomorphism $e : M_1 \cong M_2$ gives an isomorphism of commutative monoids $(M_1 \to N) \cong (M_2 \to N)$, by $f \mapsto f \circ e^{-1}$, for each commutative monoid $N$.

*Proof.* The map has the inverse $g \mapsto g \circ e$. It respects the product, because composition on the right is multiplicative by `MonoidHom.mul_comp`. $\square$

The isomorphism is `MulEquiv.monoidHomCongrLeft`. The form for the target is `MulEquiv.monoidHomCongrRight`. When $N$ is not commutative there is no product on the homomorphisms, and `MulEquiv.monoidHomCongrLeftEquiv` and `MulEquiv.monoidHomCongrRightEquiv` are equivalences of types only. The lemmas with the suffixes refl, trans and symm describe the behaviour on the identity, on composites and on inverses. The module `Mathlib.Algebra.Group.Equiv.Basic` also gives isomorphisms of function types: `MulEquiv.arrowCongr` transports along an equivalence of the domains and an isomorphism of the targets, `MulEquiv.piCongrRight` acts in each coordinate, and `MulEquiv.piUnique` and `MulEquiv.funUnique` identify a product over a type with one element with its factor. Two magmas with one element are isomorphic by `MulEquiv.ofUnique`. The permutation `Equiv.inv G` is the inverse map of a type with an involutive inverse.

The module `Mathlib.Algebra.Group.Equiv.Finite` holds the instance `Fintype.decidableEqMulEquivFintype`. When the domain is finite and the target has a decidable equality, the equality of two isomorphisms is decidable, because it is enough to compare finitely many values.

#### The graph of a homomorphism

**Definition (Graph).** The graph of a homomorphism $f : G \to H$ is the set of pairs $(x, f(x))$ in $G \times H$.

The graph is a subgroup of the product. For groups it is `MonoidHom.graph`, a `Subgroup (G × H)`, and for monoids it is `MonoidHom.mgraph`, a `Submonoid (G × H)`. The lemma `MonoidHom.mem_graph` states $(x, y) \in \operatorname{graph} f \iff f(x) = y$. The lemma `MonoidHom.graph_eq_range_prod` states that the graph is the range of the homomorphism $x \mapsto (x, f(x))$, which is `(MonoidHom.id G).prod f`.

**Theorem (Graphs among subgroups).** A subgroup $S$ of $H \times I$ is the graph of a homomorphism $H \to I$ if the first projection $S \to H$ is bijective.

*Proof.* For $h \in H$, let $f(h)$ be the second coordinate of the unique element of $S$ over $h$. The first projection is a bijective homomorphism, so its inverse is a homomorphism, and $f$ is its composite with the second projection. By construction $S$ is the graph of $f$. $\square$

The lemma is `Subgroup.exists_eq_graph`, and `Submonoid.exists_eq_mgraph` is the form for monoids. When the second projection is also bijective, `Subgroup.exists_mulEquiv_eq_graph` gives an isomorphism. The lemmas `MonoidHom.exists_range_eq_graph` and `MonoidHom.exists_mulEquiv_range_eq_graph` state the same for the range of a homomorphism into a product. These results are the setting of the lemma of Goursat for subgroups of a product.

#### Common errors

1. A learner writes `f * g` for two homomorphisms into a nonabelian group and gets an error. The instance `MonoidHom.instCommMonoid` needs a commutative target. For endomorphisms of a monoid, the product of `Monoid.End M` is the composite, which is a different operation.
2. A learner rewrites with `MonoidHom.mul_apply` in a goal about `Monoid.End M` and the rewrite fails. In `Monoid.End M` the product is composition, and the lemma to use is `Monoid.End.coe_mul`.
3. A learner tries to use `FunLike.monoid` as an instance and the instance search does not find it. It is a definition. Use it to build an instance by hand, with the injectivity of the coercion.

### Exercises

1. (A) Let $G$ be a group and $f : G \to H$ a homomorphism with $f(a) = 1$ only for $a = 1$. Prove that $f$ is injective, with `injective_iff_map_eq_one`.
2. (A) Let $A$ be an abelian group. Show that $x \mapsto x^3$ is a homomorphism $A \to A$, and compute its composite with itself in terms of `powMonoidHom`.
3. (B) Find two homomorphisms $f, g$ from $\mathbb{Z}/2$ into the symmetric group $S_3$ such that the pointwise product $x \mapsto f(x) g(x)$ is not a homomorphism.
4. (B) Show that `MonoidHom.flip` is an involution: flipping twice gives the original map. Use `MonoidHom.ext_iff₂`.
5. (B) Let $f : G \to H$ be a homomorphism of groups. Prove that the graph of $f$ is isomorphic to $G$, and find the isomorphism from `MonoidHom.graph_eq_range_prod`.
6. (C) Let $S$ be a subgroup of $H \times I$ that projects onto $H$ and onto $I$. Show that the set $N$ of $i$ with $(1, i) \in S$ is a normal subgroup of $I$, and state the lemma of Goursat for $S$.

### Reference

<?reference?>
