---
title: Central algebras, non-associative algebras and dual numbers
kind: api
modules:
  - Mathlib.Algebra.Central.Defs
  - Mathlib.Algebra.Central.Basic
  - Mathlib.Algebra.Central.End
  - Mathlib.Algebra.Central.Matrix
  - Mathlib.Algebra.Central.TensorProduct
  - Mathlib.Algebra.Algebra.IsSimpleRing
  - Mathlib.Algebra.Jordan.Basic
  - Mathlib.Algebra.NonAssoc.LieAdmissible.Defs
  - Mathlib.Algebra.NonAssoc.PreLie.Basic
  - Mathlib.Algebra.DualNumber
  - Mathlib.Algebra.DualQuaternion
explains:
  E2: [Algebra.IsCentral.center_eq_bot, Algebra.IsCentral.matrix, Algebra.IsCentral.left_of_tensor, Algebra.IsCentral.baseField_essentially_unique, commute_lmul_rmul, LeftPreLieRing.instLieAdmissibleRing, DualNumber.eps_mul_eps, DualNumber.lift, Quaternion.dualNumberEquiv]
  E1: auto
families: []
requires: [V06.C01, V06.C03, V05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Central algebras, non-associative algebras and dual numbers

### Overview

This section collects three small groups of modules that sit next to the algebras of Section 1. The first group defines a central algebra: a $K$-algebra $D$ whose center is the image of $K$. Central simple algebras over a field are the subject of the Brauer group, and the modules here give the first facts: the matrix algebra over a central algebra is central, the endomorphism algebra of a free module is central, and a tensor product is central only when its factors are.

The second group leaves associativity. A Jordan algebra satisfies a weak form of the associative law. A Lie-admissible ring is a ring whose commutator bracket satisfies the Jacobi identity, and a pre-Lie ring is a special case. These classes live on `NonUnitalNonAssocRing`, the class of rings with no unit and no associative law.

The third group defines the dual numbers $R[\varepsilon]$ with $\varepsilon^2 = 0$, as the trivial square-zero extension of $R$ by itself, and the dual quaternions. The section needs the algebras of Section 1, the trivial square-zero extensions of Section 6 and the quaternions of Section 5.

### The library around it

#### Central algebras

Let $K$ be a commutative semiring and $D$ a $K$-algebra. The center $Z(D)$ always contains the image of $K$, because the image of `algebraMap` is central. The class `Algebra.IsCentral K D` asks for the other inclusion. Its only field, `Algebra.IsCentral.out`, says `Subalgebra.center K D ≤ ⊥`, where `⊥` is the smallest subalgebra, the image of $K$. The theorem `Algebra.IsCentral.center_eq_bot` turns this into an equality, and `Algebra.IsCentral.mem_center_iff` says that a central element has the form `algebraMap K D a`. The proof of the equality is one line: `⊥ ≤ Subalgebra.center K D` holds in every algebra, and the class gives the other side.

The basic instances are short. `Algebra.IsCentral.self` says that $K$ is central over itself. `Algebra.IsCentral.instMulOpposite` gives the opposite algebra $D^{\mathrm{op}}$, which has the same center. `Algebra.IsCentral.of_algEquiv` moves the property along an isomorphism of $K$-algebras. A field $D$ that is central over $K$ is equal to $K$, since $Z(D) = D$, so the interesting examples are noncommutative.

The theorem `Algebra.IsCentral.baseField_essentially_unique` says that the base field of a central algebra is determined. Let $k \subseteq K$ be fields and $D$ a nonzero $K$-algebra that is central over $k$. Then `algebraMap k K` is bijective. Proof: the image of $K$ in $D$ is central, so it lies in the image of $k$. The map $K \to D$ is injective, because $K$ is a field and $D$ is not zero. So each element of $K$ comes from $k$.

The module `Mathlib.Algebra.Algebra.IsSimpleRing` has one instance, `instFaithfulSMul_1`. It says that a simple commutative ring $R$ acts faithfully on every nontrivial $R$-algebra. The reason: the kernel of `algebraMap R A` is an ideal, so it is $0$ or $R$, and it is not $R$ because $1 \neq 0$ in $A$.

#### Matrices and endomorphisms

The matrix algebra over a central algebra is central. The theorem `Matrix.subalgebraCenter_eq_scalarAlgHom_map` computes the center of $M_n(A)$ for any $R$-algebra $A$: it is the image of the center of $A$ under the scalar matrices $a \mapsto a I$. The instance `Algebra.IsCentral.matrix` follows. Proof sketch: a matrix $M$ that commutes with each matrix unit $E_{ij}$ is diagonal with equal diagonal entries, so $M = aI$. Then $M$ commutes with $bI$ for each $b \in A$, so $a$ is central in $A$, so $a$ comes from $K$.

The module `Mathlib.Algebra.Central.End` treats $\operatorname{End}_R(M)$ for a free $R$-module $M$. The theorem `Module.End.mem_subalgebraCenter_iff` says that a central endomorphism is multiplication by a central element $\alpha$ of $R$, written `Module.End.smulLeft α hα`. The instance `Algebra.IsCentral.instEnd` deduces that $\operatorname{End}_R(M)$ is central over $S$ when $R$ is central over $S$. The theorem `LinearEquiv.conjAlgEquiv_ext_iff` is the Skolem-Noether type statement in this setting: two linear isomorphisms $f, g : M \to M_2$ give the same conjugation map $\operatorname{End}(M) \to \operatorname{End}(M_2)$ exactly when $f = \alpha g$ for a scalar $\alpha$.

#### Tensor products

The module `Mathlib.Algebra.Central.TensorProduct` proves that the factors of a central tensor product are central. The theorem `Algebra.IsCentral.left_of_tensor` takes $K$-algebras $B$ and $C$ with $B$ flat over $K$ and `algebraMap K C` injective. If $B \otimes_K C$ is central, then $B$ is central. The theorem `Algebra.IsCentral.right_of_tensor` is the mirror form, with $C$ flat and `algebraMap K B` injective. Proof sketch: the map $b \mapsto b \otimes 1$ sends $Z(B)$ into the center of $B \otimes_K C$, by `Algebra.TensorProduct.includeLeft_map_center_le`. So for $b \in Z(B)$ there is $a \in K$ with $b \otimes 1 = a \cdot 1 \otimes 1 = (a \cdot 1) \otimes 1$. The map $b \mapsto b \otimes 1$ is injective, because $B$ is flat and $K \to C$ is injective. So $b = a \cdot 1$. Over a field every module is flat, and a nonzero algebra has an injective structure map, so `Algebra.IsCentral.left_of_tensor_of_field` asks only that $C$ is nontrivial.

#### Jordan algebras

A Jordan multiplication satisfies the Jordan identity $(ab)(aa) = a(b(aa))$ but not the associative law. The class `IsJordan A` lives on a type with a multiplication `Mul A` and asks for five identities, because $A$ need not be commutative: `IsJordan.lmul_comm_rmul` is $(ab)a = a(ba)$, `IsJordan.lmul_comm_rmul_rmul` is $(ab)(aa) = a(b(aa))$, and three more forms. The class `IsCommJordan A` lives on a commutative magma and asks only for the Jordan identity; the instance `IsCommJordan.toIsJordan` gives the other identities by commutativity. The instances `Semigroup.isJordan` and `CommSemigroup.isCommJordan` say that every associative multiplication is Jordan.

The identities have a form in terms of the multiplication operators $L_a(x) = ax$ and $R_a(x) = xa$, written `AddMonoid.End.mulLeft a` and `AddMonoid.End.mulRight a`. The theorem `commute_lmul_rmul` says that $L_a$ and $R_a$ commute; this is the identity $(ax)a = a(xa)$ for all $x$. The theorems `commute_lmul_lmul_sq`, `commute_lmul_rmul_sq`, `commute_lmul_sq_rmul` and `commute_rmul_rmul_sq` are the other identities in operator form. For a commutative Jordan ring, `two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add` and `two_nsmul_lie_lmul_lmul_add_add_eq_zero` are the linearized Jordan identity, with the commutator bracket of operators. A factor $2$ appears because linearization replaces $a$ by $a + b$, and the cross terms come twice.

#### Lie-admissible and pre-Lie rings

The associator of three elements is $\operatorname{assoc}(x, y, z) = (xy)z - x(yz)$, written `associator x y z`. It is zero for all arguments exactly when the ring is associative. The commutator $[x, y] = xy - yx$ satisfies the Jacobi identity in an associative ring. In a general ring, the Jacobi identity holds exactly when the sum of the associators over the even permutations of $(x, y, z)$ equals the sum over the odd ones.

The class `LieAdmissibleRing L` asks for this identity on a `NonUnitalNonAssocRing`. The instance `LieAdmissibleRing.instLieRing` then makes $L$ a Lie ring with $[x, y] = xy - yx$, and `LieAdmissibleAlgebra.instLieAlgebra` does the same for an algebra over a commutative ring. The instance `Ring.instLieAdmissibleRing` says that an associative ring is Lie-admissible, because all associators are zero.

A left pre-Lie ring is a ring with $\operatorname{assoc}(x, y, z) = \operatorname{assoc}(y, x, z)$. The class is `LeftPreLieRing`, with the rule `LeftPreLieRing.assoc_symm`. The class `RightPreLieRing` asks for symmetry in the last two arguments, `RightPreLieRing.assoc_symm`. The opposite ring swaps the two kinds: `LeftPreLieRing.instRightPreLieRingMulOpposite` and `RightPreLieRing.instLeftPreLieRingMulOpposite`. The classes `LeftPreLieAlgebra` and `RightPreLieAlgebra` add a compatible module structure over a commutative ring.

The instance `LeftPreLieRing.instLieAdmissibleRing` says that a left pre-Lie ring is Lie-admissible. Proof: the left symmetry pairs each even permutation with an odd one. It gives $\operatorname{assoc}(x,y,z) = \operatorname{assoc}(y,x,z)$, $\operatorname{assoc}(z,x,y) = \operatorname{assoc}(x,z,y)$ and $\operatorname{assoc}(y,z,x) = \operatorname{assoc}(z,y,x)$. Add the three equalities: the left side is the even sum and the right side is the odd sum. A typical example is the space of vector fields on $\mathbb{R}^n$ with $(f \triangleright g) = \sum_i f_i \partial_i g$.

#### Dual numbers

The ring of dual numbers over $R$ is $R[\varepsilon] = R \oplus R\varepsilon$ with $\varepsilon^2 = 0$. Mathlib defines `DualNumber R` as an abbreviation for `TrivSqZeroExt R R`, so the whole API of Section 6 applies. The element $\varepsilon$ is `DualNumber.eps`, with the notation `ε` and the notation `R[ε]` for the type. Its parts are `DualNumber.fst_eps` and `DualNumber.snd_eps`: the real part is $0$ and the dual part is $1$.

| Lean name | Statement |
| --- | --- |
| `DualNumber.eps_mul_eps` | $\varepsilon \cdot \varepsilon = 0$ |
| `DualNumber.eps_pow_two` | $\varepsilon^2 = 0$ |
| `DualNumber.inr_eq_smul_eps` | the element $(0, r)$ is $r \cdot \varepsilon$ |
| `DualNumber.snd_mul` | the dual part of $xy$ is $x_0 y_1 + x_1 y_0$ |
| `DualNumber.commute_eps_left` | $\varepsilon$ commutes with every $x$ |
| `DualNumber.inv_eps` | over a division ring, $\varepsilon^{-1} = 0$ |

The rule `DualNumber.snd_mul` is the product rule of calculus. For a polynomial $p$, the value $p(a + \varepsilon)$ is $p(a) + p'(a)\varepsilon$, because every term with $\varepsilon^2$ vanishes. This makes dual numbers a model for first-order derivatives. The inverse in `DualNumber.inv_eps` is the junk value of the inverse from Section 6, since $\varepsilon$ is not a unit.

The universal property is `DualNumber.lift`. An $R$-algebra map $A[\varepsilon] \to B$ is the same as a pair $(f, e)$ of an algebra map $f : A \to B$ and an element $e \in B$ with $e^2 = 0$ that commutes with each $f(a)$. The forward direction sends $a + a'\varepsilon$ to $f(a) + f(a')e$; the conditions make this map multiplicative, as the computation $(f(a) + f(a')e)(f(b) + f(b')e) = f(ab) + (f(a)f(b') + f(a')f(b))e$ shows. The lemmas `DualNumber.lift_apply_eps` and `DualNumber.lift_apply_inl` give the values on $\varepsilon$ and on $A$. The extension lemma `DualNumber.algHom_ext` says that two $R$-algebra maps from $R[\varepsilon]$ agree when they agree on $\varepsilon$, and `DualNumber.ringHom_ext` is the form for ring maps on a commutative base. The theorem `DualNumber.range_inlAlgHom_sup_adjoin_eps` says that $A[\varepsilon]$ is generated by $A$ and $\varepsilon$.

#### Dual quaternions

The dual quaternions are the quaternions with dual number coefficients. They model rigid motions of space. The equivalence `Quaternion.dualNumberEquiv` is an $R$-algebra isomorphism $\mathbb{H}[R[\varepsilon]] \cong (\mathbb{H}[R])[\varepsilon]$. It sends $q$ with components $q_r, q_i, q_j, q_k \in R[\varepsilon]$ to the dual number whose real part collects the real parts of the four components and whose dual part collects the dual parts. The simp lemmas have names such as `Quaternion.re_fst_dualNumberEquiv` and `Quaternion.fst_imI_dualNumberEquiv_symm`, one for each pair of a quaternion part and a dual part. The map is multiplicative because the quaternion multiplication is given by the same polynomial formulas in the components over any commutative ring, and $\varepsilon$ is central.

#### Common errors

1. `Algebra.IsCentral K D` is about the center of $D$ as a $K$-subalgebra. It says nothing about simplicity. A central simple algebra needs `IsSimpleRing D` as well.
2. `DualNumber R` is reducible to `TrivSqZeroExt R R`, so its parts are `TrivSqZeroExt.fst` and `TrivSqZeroExt.snd`. The namespace `DualNumber` has no projections of its own; it holds the lemmas about `DualNumber.eps` and the universal property.
3. The Jordan classes need only `Mul A`, but the operator lemmas such as `commute_lmul_rmul` need a `NonUnitalNonAssocRing`. A Jordan algebra over a field uses this ring class, not `Ring`, because `Ring` includes associativity.

### Exercises

1. (A) Prove from `Algebra.IsCentral.center_eq_bot` that a commutative $K$-algebra $D$ that is central over $K$ has `algebraMap K D` surjective.
2. (A) Compute $(a + b\varepsilon)(c + d\varepsilon)$ in $R[\varepsilon]$ and check the result against `DualNumber.snd_mul`.
3. (B) Prove that $a + b\varepsilon$ is a unit in $R[\varepsilon]$ exactly when $a$ is a unit in $R$, and give its inverse.
4. (B) Show that the polynomial evaluation $p(a + \varepsilon)$ equals $p(a) + p'(a)\varepsilon$ for $p \in R[X]$, by induction on $p$.
5. (B) Show that every associative ring satisfies the left pre-Lie identity, and deduce `Ring.instLieAdmissibleRing` from `LeftPreLieRing.instLieAdmissibleRing` for such rings.
6. (C) Prove that a matrix in $M_n(D)$ that commutes with all matrix units is a scalar matrix $aI$ with $a$ central in $D$.

### Reference

<?reference?>
