---
title: Monoid algebras
kind: api
modules:
  - Mathlib.Algebra.MonoidAlgebra.Defs
  - Mathlib.Algebra.MonoidAlgebra.Lift
  - Mathlib.Algebra.MonoidAlgebra.Basic
  - Mathlib.Algebra.MonoidAlgebra.Opposite
  - Mathlib.Algebra.MonoidAlgebra.PointwiseSMul
  - Mathlib.Algebra.MonoidAlgebra.Cardinal
explains:
  E2: [MonoidAlgebra.single_mul_single, MonoidAlgebra.coeff_mul_antidiag, MonoidAlgebra.coeff_single_one_mul, MonoidAlgebra.liftNC_mul, MonoidAlgebra.lift, MonoidAlgebra.algHom_ext, MonoidAlgebra.curryRingEquiv, MonoidAlgebra.opRingEquiv, MonoidAlgebra.smul_apply_mulAction, MonoidAlgebra.cardinalMk_of_fintype]
  E1: auto
families: []
requires: [V06.C05, V09.C05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Monoid algebras

### Overview

Let $R$ be a semiring and $M$ a monoid. The monoid algebra $R[M]$ is the free $R$-module on the set $M$, with the product that extends the product of $M$ by bilinearity. An element is a finite sum $\sum_m r_m \, m$, and $(r \, m)(s \, n) = (rs) \, (mn)$. The group ring $\mathbb{Z}[G]$ and the group algebra $k[G]$ of representation theory are the cases where $M$ is a group. When $M$ is written additively, the same construction gives the additive monoid algebra, and Mathlib builds its polynomial rings on it: `Polynomial R` comes from the exponents in $\mathbb{N}$, and `MvPolynomial σ R` comes from the exponent vectors in `σ →₀ ℕ`.

This section covers the definition, the ring and algebra structures, and the universal properties. Section 9 continues with maps between monoid algebras, the module structure, supports, degrees, division and gradings. A reader who works with polynomials meets these files when a lemma about `Polynomial` or `MvPolynomial` is proved once for all monoid algebras.

### The library around it

#### Two structures and one set of lemmas

The file `Mathlib.Algebra.MonoidAlgebra.Defs` defines two types. `MonoidAlgebra R M` is for a multiplicative $M$ and `AddMonoidAlgebra R M` is for an additive $M$. Each one is a structure with one field. The constructor `MonoidAlgebra.ofCoeff` takes a finitely supported function `M →₀ R`, and the projection `MonoidAlgebra.coeff` gives it back. The lemmas `MonoidAlgebra.coeff_ofCoeff` and `MonoidAlgebra.ofCoeff_coeff` say that the two maps are inverse, and `MonoidAlgebra.coeffEquiv` and `MonoidAlgebra.coeffAddEquiv` bundle them as an equivalence and an additive isomorphism. The extensionality lemma `MonoidAlgebra.ext` says that two elements with the same coefficients are equal.

The structure is a wall between the two products. A plain `Finsupp` carries the pointwise product of functions. The structure makes sure that the only product on `MonoidAlgebra R M` is the convolution product. So the coefficient of $x$ at $m$ is always written `x.coeff m`, and the simp lemmas move `MonoidAlgebra.coeff` through sums, scalar products and products: `MonoidAlgebra.coeff_add`, `MonoidAlgebra.coeff_smul`, `MonoidAlgebra.coeff_neg`, `MonoidAlgebra.coeff_sub`.

The additive version is not written by hand. Each definition and lemma of the multiplicative version carries the attribute `to_additive`, which generates the additive copy. The rule of names is the usual one: `MonoidAlgebra.single_mul_single` becomes `AddMonoidAlgebra.single_mul_single`, with $m_1 m_2$ replaced by $m_1 + m_2$, and a lemma about `1 : M` becomes a lemma about `0 : M`. For example `MonoidAlgebra.coeff_one_one` becomes `AddMonoidAlgebra.coeff_one_zero`. The attribute `dont_translate := R` keeps the product of the coefficient ring multiplicative. So in `AddMonoidAlgebra.single_pow` the exponent becomes $n \cdot m$ but the coefficient stays $r^n$. Both types have the scoped notation `R[M]`, which reads as `MonoidAlgebra R M` when the namespace `MonoidAlgebra` is open and as `AddMonoidAlgebra R M` when `AddMonoidAlgebra` is open.

#### Single elements and the product

The element `MonoidAlgebra.single` $m$ $r$ is $r \, m$, the function with value $r$ at $m$ and $0$ elsewhere. The lemmas `MonoidAlgebra.single_zero` and `MonoidAlgebra.single_add` say that it is additive in $r$, `MonoidAlgebra.coeff_single` gives its coefficients, and `MonoidAlgebra.sum_coeff_single` says that every element is the sum of the single elements of its coefficients. The decomposition `MonoidAlgebra.single_add_erase` splits off one term with `MonoidAlgebra.erase`.

The product is defined by `MonoidAlgebra.mul_def`:
$$x \, y = \sum_{m_1} \sum_{m_2} x(m_1) \, y(m_2) \, (m_1 m_2).$$
It needs only a multiplication on $M$, so `MonoidAlgebra R M` is a nonunital, nonassociative semiring for a magma $M$, a semiring for a monoid, a ring when $R$ is a ring, and commutative when $R$ and $M$ are commutative. The unit is `single 1 1` (`MonoidAlgebra.one_def`). The rule on single elements is `MonoidAlgebra.single_mul_single`: $(r_1 \, m_1)(r_2 \, m_2) = (r_1 r_2) \, (m_1 m_2)$. Proof: each of the two sums in `MonoidAlgebra.mul_def` has one term. Then `MonoidAlgebra.single_pow` follows by induction on $n$.

The coefficient of a product is the convolution sum. The lemma `MonoidAlgebra.coeff_mul` writes it as a double sum with a condition $m_1 m_2 = m$, and `MonoidAlgebra.coeff_mul_antidiag` writes it as a sum over any finite set $s$ of pairs whose members are exactly the pairs with product $m$:
$$(xy)(m) = \sum_{(p_1, p_2) \in s} x(p_1) \, y(p_2).$$
Proof: in the double sum of `MonoidAlgebra.coeff_mul`, the nonzero terms are indexed by the pairs in the supports with $p_1 p_2 = m$. These pairs lie in $s$, and the other pairs of $s$ give zero terms. For polynomials, $s$ is the antidiagonal $\{(i, j) : i + j = n\}$ of $\mathbb{N}$.

A product with a single element has a simpler coefficient. The lemma `MonoidAlgebra.coeff_single_one_mul` says $(r \cdot 1 \cdot x)(m) = r \, x(m)$, and `MonoidAlgebra.coeff_mul_single_one` is the version on the right. Proof: in `MonoidAlgebra.coeff_mul_antidiag` take $s$ as the set of pairs $(1, n)$ with $n = m$, which is the only pair with first entry in the support of `single 1 r` and product $m$. Over a cancellative monoid, `MonoidAlgebra.coeff_mul_single_mul` gives $(x \cdot r \, m)(m' m) = x(m') \, r$. Over a group, `MonoidAlgebra.coeff_mul_single_apply` gives $(x \cdot r \, g)(h) = x(h g^{-1}) \, r$, and `MonoidAlgebra.coeff_mul_apply_left` writes a general coefficient as a sum over the support of $x$ alone.

The maps into the monoid algebra are bundled. `MonoidAlgebra.of` is the monoid homomorphism $m \mapsto 1 \, m$ (`MonoidAlgebra.of_apply`), and it is injective over a nontrivial ring (`MonoidAlgebra.of_injective`). `MonoidAlgebra.ofMagma` is the version for a magma. `MonoidAlgebra.singleOneRingHom` is the ring homomorphism $r \mapsto r \, 1$, and the additive version is `AddMonoidAlgebra.singleZeroRingHom`. For the additive version `AddMonoidAlgebra.of` has domain `Multiplicative M`, because a monoid homomorphism needs a multiplicative source. Two ring homomorphisms out of $R[M]$ that agree on the elements $r \, 1$ and $1 \, m$ are equal (`MonoidAlgebra.ringHom_ext`). For induction, `MonoidAlgebra.induction_on` reduces a statement to the elements $1 \, m$, sums and scalar multiples.

Two isomorphisms in this file change the monoid. `MonoidAlgebra.uniqueRingEquiv` identifies $R[M]$ with $R$ when $M$ is trivial. `MonoidAlgebra.curryRingEquiv` identifies $R[M \times N]$ with $R[N][M]$. Proof sketch: send $r \, (m, n)$ to $(r \, n) \, m$. This map is additive and bijective on the single elements, and it respects `MonoidAlgebra.single_mul_single` because the product of $M \times N$ is taken in each factor. This is the form of $R[x, y] = R[y][x]$ for monoid algebras.

#### Lifts

The file `Mathlib.Algebra.MonoidAlgebra.Lift` defines the general lift `MonoidAlgebra.liftNC`. It takes an additive map $f \colon R \to S$ and any function $g \colon M \to S$ into a semiring, and sends $\sum r_m \, m$ to $\sum f(r_m) \, g(m)$. On single elements it is $f(r) \, g(m)$ (`MonoidAlgebra.liftNC_single`). The letters NC mean "not commutative": the lift is multiplicative only when the values of $f$ commute with the values of $g$. This is the content of `MonoidAlgebra.liftNC_mul`. Proof: by additivity, it is enough to check two single elements. Then $f(r_1 r_2) \, g(m_1 m_2) = f(r_1) f(r_2) g(m_1) g(m_2)$, and the hypothesis lets $f(r_2)$ move past $g(m_1)$. When $f$ is a ring homomorphism, $g$ a monoid homomorphism, and all values commute, `MonoidAlgebra.liftNCRingHom` is the resulting ring homomorphism, with `MonoidAlgebra.liftNCRingHom_single` as its value on single elements.

#### The algebra structure and the universal property

The file `Mathlib.Algebra.MonoidAlgebra.Basic` works over a commutative semiring $R$ and an $R$-algebra $A$. The instance `MonoidAlgebra.algebra` makes `MonoidAlgebra A M` an $R$-algebra, with `algebraMap` given by $r \mapsto (\text{algebraMap } r) \, 1$ (`MonoidAlgebra.coe_algebraMap`). The map `MonoidAlgebra.singleOneAlgHom` is the algebra map $A \to A[M]$.

The universal property is `MonoidAlgebra.lift`. It is an equivalence between monoid homomorphisms $M \to A$ and $R$-algebra homomorphisms $R[M] \to A$:
$$\operatorname{Hom}_{\text{Mon}}(M, A) \cong \operatorname{Hom}_{R\text{-Alg}}(R[M], A).$$
The algebra map sends $r \, m$ to $r \cdot F(m)$ (`MonoidAlgebra.lift_single`), so it extends $F$ (`MonoidAlgebra.lift_of`). Proof: given $F$, use `MonoidAlgebra.liftNCRingHom` with the algebra map of $R$ and $F$. The values of `algebraMap` are central in $A$, so they commute with the values of $F$. The inverse map restricts an algebra homomorphism along `MonoidAlgebra.of`. The two maps are inverse because an algebra homomorphism is fixed by its values on the elements $1 \, m$, by `MonoidAlgebra.lift_unique`. This is the universal property of the group algebra that representation theory uses: a representation of $G$ on $V$ is the same as a $k[G]$-module structure on $V$.

The extensionality lemma `MonoidAlgebra.algHom_ext` says that two $R$-algebra homomorphisms out of $A[M]$ are equal when they agree on the elements $1 \, m$ and on $A$ through `MonoidAlgebra.singleOneAlgHom`. The version `MonoidAlgebra.liftNCAlgHom` lifts an algebra homomorphism of $A$ and a monoid homomorphism of $M$ with commuting values. For a magma $M$ and a nonunital algebra $A$, `MonoidAlgebra.liftMagma` is the universal property of the nonunital, nonassociative algebra of a magma.

The rest of the file builds algebra maps from maps of the arguments.

| Lean name | Statement |
| --- | --- |
| `MonoidAlgebra.mapAlgHom` | an algebra map $A \to B$ gives $A[M] \to B[M]$ |
| `MonoidAlgebra.mapAlgEquiv` | an algebra isomorphism $A \cong B$ gives $A[M] \cong B[M]$ |
| `MonoidAlgebra.domCongr` | a monoid isomorphism $M \cong N$ gives $A[M] \cong A[N]$ |
| `MonoidAlgebra.mapDomainAlgHom` | a monoid map $M \to N$ gives $A[M] \to A[N]$ |
| `MonoidAlgebra.domCongrAut` | the action of the automorphisms of $M$ on $A[M]$ |
| `MonoidAlgebra.curryAlgEquiv` | $A[M \times N] \cong A[N][M]$ as algebras |
| `MonoidAlgebra.commAlgEquiv` | $A[M][N] \cong A[N][M]$ |
| `MonoidAlgebra.uniqueAlgEquiv` | $A[M] \cong A$ for a trivial $M$ |
| `MonoidAlgebra.toAdditiveAlgEquiv` | $A[M] \cong A[\text{Additive } M]$ |

The last line and `AddMonoidAlgebra.toMultiplicativeAlgEquiv` go between the two kinds of monoid algebra. They are useful when a result exists for only one kind. For two commutative semirings $R \to S$ and a commutative monoid $M$, `MonoidAlgebra.algebraMonoidAlgebra` makes $S[M]$ an algebra over $R[M]$.

#### The opposite ring

The file `Mathlib.Algebra.MonoidAlgebra.Opposite` gives the ring isomorphism `MonoidAlgebra.opRingEquiv` between the opposite ring of $R[M]$ and $R^{\text{op}}[M^{\text{op}}]$. It sends $r \, m$ to $r^{\text{op}} \, m^{\text{op}}$ (`MonoidAlgebra.opRingEquiv_single`). Proof: on single elements, the product in the opposite ring is $(r_2 r_1) \, (m_2 m_1)$, and this is the product of $r_1^{\text{op}} \, m_1^{\text{op}}$ and $r_2^{\text{op}} \, m_2^{\text{op}}$ in $R^{\text{op}}[M^{\text{op}}]$. The additive version is `AddMonoidAlgebra.opRingEquiv`. For a group $G$, composing with the inverse map gives the standard isomorphism of $k[G]$ with its opposite.

#### Convolution with functions

The file `Mathlib.Algebra.MonoidAlgebra.PointwiseSMul` defines a scoped action of $R[G]$ on functions $P \to V$, where $G$ acts on a set $P$ by a left cancellative action and $V$ is an $R$-module. The value of $f \cdot x$ at $p$ is the sum of $f(g) \cdot x(q)$ over the pairs $(g, q)$ with $g \cdot q = p$ (`MonoidAlgebra.smul_eq`). For a group acting on $P$, `MonoidAlgebra.smul_apply_mulAction` gives the familiar formula
$$(f \cdot x)(p) = \sum_{g} f(g) \cdot x(g^{-1} p).$$
Proof: for a group action the pair is fixed by $g$, since $q = g^{-1} p$. The lemma `MonoidAlgebra.mem_smulAntidiagonal_of_group` says this, and the sum over pairs becomes a sum over the support of $f$. The action is scoped, so it is active only when the namespace is open.

#### Cardinality

The file `Mathlib.Algebra.MonoidAlgebra.Cardinal` computes the cardinal of $R[M]$. For a finite $M$, `MonoidAlgebra.cardinalMk_of_fintype` says $\#R[M] = \#R^{\#M}$, because an element is any function $M \to R$. For an infinite $M$ and a nontrivial $R$, `MonoidAlgebra.cardinalMk_of_infinite` says $\#R[M] = \max(\#R, \#M)$, as for finitely supported functions. The versions with `lift` allow $R$ and $M$ in different universes, and each lemma has an additive copy, for example `AddMonoidAlgebra.cardinalMk_of_infinite`.

#### Common errors

1. Treating an element of `MonoidAlgebra R M` as a function. It is a structure, so `x m` does not typecheck. Write `x.coeff m`, and use the `MonoidAlgebra.coeff` lemmas for rewriting.
2. Expecting `AddMonoidAlgebra.of` to have domain $M$. Its domain is `Multiplicative M`. In proofs about polynomials, the single elements `AddMonoidAlgebra.single` are usually easier to use.
3. Forgetting the commutation hypothesis of `MonoidAlgebra.liftNC_mul`. Over a noncommutative target, a lift is multiplicative only when the images of the coefficients commute with the images of the monoid. Over a commutative base, `MonoidAlgebra.lift` takes care of this.

### Exercises

1. (A) Use `MonoidAlgebra.single_mul_single` to compute $(1 \, g + 1 \, h)^2$ in $\mathbb{Z}[G]$ for elements $g, h$ of a group, and say when it is $1 \, g^2 + 2 \, gh + 1 \, h^2$.
2. (A) Show that $\sum_{g \in G} 1 \, g$ is central in $k[G]$ for a finite group $G$, and compute its square.
3. (B) Show that `MonoidAlgebra.lift` sends the trivial homomorphism $G \to k$ to the augmentation map $\sum r_g \, g \mapsto \sum r_g$, and that its kernel is spanned by the elements $1 \, g - 1$.
4. (B) Prove that $k[\mathbb{Z}/n\mathbb{Z}]$ is isomorphic to $k[X]/(X^n - 1)$ as a $k$-algebra, with `MonoidAlgebra.lift` for one direction.
5. (B) Use `MonoidAlgebra.cardinalMk_of_fintype` to count the elements of $\mathbb{F}_2[G]$ for a group $G$ of order $4$.
6. (C) Prove that for a nontrivial finite group $G$ and a field $k$, the ring $k[G]$ has a zero divisor.

### Reference

<?reference?>
