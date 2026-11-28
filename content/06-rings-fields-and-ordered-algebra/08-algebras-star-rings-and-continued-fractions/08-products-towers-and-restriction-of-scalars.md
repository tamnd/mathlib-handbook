---
title: Products, opposites, towers and restriction of scalars
kind: api
modules:
  - Mathlib.Algebra.Algebra.Pi
  - Mathlib.Algebra.Algebra.Prod
  - Mathlib.Algebra.Algebra.Opposite
  - Mathlib.Algebra.Algebra.Tower
  - Mathlib.Algebra.Algebra.RestrictScalars
  - Mathlib.Algebra.Algebra.Bilinear
  - Mathlib.Algebra.Algebra.Epi
explains:
  E2: [Pi.algebra, AlgHom.prodEquiv, AlgHom.fromOpposite, AlgEquiv.moduleEndSelf, IsScalarTower.algebraMap_eq, AlgHom.restrictScalars, RestrictScalars.algebra, Algebra.lmul_isUnit_iff, Algebra.isEpi_iff_forall_one_tmul_eq, Algebra.isEpi_iff_surjective_algebraMap_of_finite]
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

## Products, opposites, towers and restriction of scalars

### Overview

This section builds new algebras from old ones and moves algebras between rings of scalars. The product of a family of $R$-algebras is an $R$-algebra, and so is the opposite algebra. A tower $R \to S \to A$ of algebras makes each $S$-algebra homomorphism an $R$-algebra homomorphism. The type synonym `RestrictScalars R S M` gives an $S$-module the $R$-module structure by restriction, in a form that instance search can handle.

The last two modules study the multiplication itself. The multiplication of an $R$-algebra is an $R$-bilinear map, and the left multiplication $a \mapsto L_a$ is an algebra homomorphism $A \to \operatorname{End}_R(A)$. An epimorphism of commutative rings $R \to A$ is a map that can be cancelled on the right; the class `Algebra.IsEpi` describes it by a condition on the tensor product. The section needs Section 1 and the groups of Volume 5. Volume 7 treats modules in full.

### The library around it

#### Products

Let $(A_i)_{i \in I}$ be a family of $R$-algebras. The instance `Pi.algebra` makes the product $\prod_i A_i$ an $R$-algebra with the operations taken in each coordinate. Its structure map is $r \mapsto (\operatorname{algebraMap}(r))_i$. The only thing to check is that the image is central, and this holds in each coordinate. The instance `Function.algebra` is the case of a constant family, the functions $I \to A$.

The product has its universal property in algebra homomorphisms. The projection `Pi.evalAlgHom R A i` is the evaluation at $i$. A family of maps $f_i : B \to A_i$ gives `AlgHom.pi f : B → ∏ A i`, and `AlgHom.pi_evalAlgHom` says that this is the identity for the projections. Some maps of functions follow. `Pi.constAlgHom R A B` sends $b$ to the constant function. `AlgHom.compLeft f ι` applies $f$ in each coordinate. The equivalences `AlgEquiv.piCongrRight`, `AlgEquiv.piCongrLeft`, `AlgEquiv.funUnique` and `AlgEquiv.sumArrowEquivProdArrow` change the factors, reindex the product, remove a product over a type with one element, and split a product over $\alpha \oplus \beta$ into two.

The binary product works in the same way. The instance `Prod.algebra` makes $A \times B$ an $R$-algebra. The projections are `AlgHom.fst` and `AlgHom.snd`, and a pair of maps gives `AlgHom.prod f g`. The equivalence `AlgHom.prodEquiv` states the universal property: $(A \to B) \times (A \to C) \simeq (A \to B \times C)$ in algebra homomorphisms. Proof: send $(f, g)$ to $a \mapsto (f(a), g(a))$ and $h$ to $(\pi_1 \circ h, \pi_2 \circ h)$; the lemmas `AlgHom.fst_prod`, `AlgHom.snd_prod` and `AlgHom.prod_fst_snd` say that these maps are inverse. `AlgHom.prodMap`, `AlgEquiv.prodCongr`, `AlgEquiv.prodUnique` and `AlgEquiv.uniqueProd` complete the API.

#### Opposite algebras

The opposite ring $A^{\mathrm{op}}$ has the product $a * b = ba$. The instance `MulOpposite.instAlgebra` makes it an $R$-algebra; the structure map stays central. The equivalence `AlgHom.op` identifies the maps $A \to B$ with the maps $A^{\mathrm{op}} \to B^{\mathrm{op}}$, and `AlgEquiv.op` does the same for isomorphisms. The isomorphism `AlgEquiv.opOp` identifies $A$ with $(A^{\mathrm{op}})^{\mathrm{op}}$, and `AlgEquiv.opComm` moves the opposite from one side of an isomorphism to the other. `AlgEquiv.piMulOpposite` says that the opposite of a product is the product of the opposites.

A map $f : A \to B$ whose image is commutative gives a map from the opposite. `AlgHom.fromOpposite f h` is the map $A^{\mathrm{op}} \to B$ with the same function, where $h$ says that $f(x)$ and $f(y)$ commute for all $x, y$. Proof: $f(x * y) = f(yx) = f(y) f(x) = f(x) f(y)$, by $h$. The map `AlgHom.toOpposite` is the version with values in $B^{\mathrm{op}}$.

The endomorphisms of $A$ as a module over itself are the right multiplications. The isomorphism `AlgEquiv.moduleEndSelf R` identifies $A^{\mathrm{op}}$ with `Module.End A A`: an element $a$ goes to the map $x \mapsto xa$. The opposite appears because $x(ab) = (xa)b$, so the right multiplication by $ab$ is $R_{ab} = R_b \circ R_a$, with the factors in the reverse order. Proof that every endomorphism is of this form: an $A$-linear map $\phi$ satisfies $\phi(x) = \phi(x \cdot 1) = x \phi(1)$. The companion `AlgEquiv.moduleEndSelfOp` identifies $A$ with `Module.End Aᵐᵒᵖ A`.

#### Towers of algebras

A tower $R \to S \to A$ is three algebras with the class `IsScalarTower R S A`, which says $(r \cdot s) \cdot a = r \cdot (s \cdot a)$. The theorem `IsScalarTower.algebraMap_eq` says that the structure maps compose: $\operatorname{algebraMap}_{RA} = \operatorname{algebraMap}_{SA} \circ \operatorname{algebraMap}_{RS}$. Proof: $\operatorname{algebraMap}_{RA}(r) = r \cdot 1_A = (r \cdot 1_S) \cdot 1_A = \operatorname{algebraMap}_{SA}(\operatorname{algebraMap}_{RS}(r))$. The theorem `IsScalarTower.of_algebraMap_eq` is the converse, and `IsScalarTower.of_algHom` builds a tower from an algebra homomorphism.

An $S$-algebra homomorphism of a tower is an $R$-algebra homomorphism. `AlgHom.restrictScalars R f` is this map, with the same function by `AlgHom.coe_restrictScalars`, and `AlgHom.restrictScalars_injective` says that no information is lost. `AlgEquiv.restrictScalars` and the group homomorphism `AlgEquiv.restrictScalarsHom` do the same for isomorphisms. When $R \to S$ is surjective the converse also holds: `AlgHom.extendScalarsOfSurjective` and `AlgEquiv.extendScalarsOfSurjective` turn an $R$-algebra map back into an $S$-algebra map, since every $s$ is the image of some $r$. In this case `Submodule.orderIsoOfAlgebraMapSurjective` identifies the $S$-submodules of $M$ with its $R$-submodules.

The module `Mathlib.Algebra.Algebra.Tower` also has lemmas on spans in a tower. `Submodule.span_smul_of_span_eq_top` says that when $s$ spans $S$ over $R$, the products $s \cdot t$ span over $R$ the $S$-span of $t$. This is the key step in the tower law for finite generation. `Submodule.restrictScalars_span` says that the $S$-span and the $R$-span of a set agree when $R \to S$ is surjective. The algebra homomorphism `Algebra.lsmul R B M` sends $a$ to the scalar action $m \mapsto a \cdot m$, as an element of `Module.End B M`.

#### Restriction of scalars

Let $S$ be an $R$-algebra and $M$ an $S$-module. Then $M$ is an $R$-module by $r \cdot m = \operatorname{algebraMap}(r) \cdot m$. The definition `Module.restrictScalars R S M` gives this structure, and `Algebra.restrictScalars` does the same for an $S$-algebra. These are not instances, because an instance would make the $R$-module structure on $M$ depend on a choice of $S$ and cause clashes with an existing $R$-module structure.

The type synonym `RestrictScalars R S M` solves this. It is equal to $M$ by definition, but instance search treats it as a new type. The instances `RestrictScalars.module` and `RestrictScalars.algebra` put the restricted structures on it, `RestrictScalars.moduleOrig` keeps the original $S$-module structure, and `RestrictScalars.isScalarTower` makes the tower $R \to S \to$ `RestrictScalars R S M`. The maps `RestrictScalars.addEquiv` and `RestrictScalars.ringEquiv` identify the synonym with $M$, and `RestrictScalars.addEquiv_map_smul` says that this identification respects the actions. Use the synonym when a construction needs an $R$-module and only the $S$-module is at hand, for example a field extension $L / K$ seen as a vector space over a subfield of $K$.

#### The multiplication as a bilinear map

The multiplication of an $R$-algebra $A$ is bilinear. The map `LinearMap.mul R A` is $a \mapsto (b \mapsto ab)$ as an element of $A \to_R A \to_R A$, and `LinearMap.mul' R A` is the induced map $A \otimes_R A \to A$. The theorem `LinearMap.map_mul_iff` says that a linear map $f$ is multiplicative exactly when $f \circ \mu_A = \mu_B \circ (f \times f)$, in the curried form. The left and right multiplications `LinearMap.mulLeft R a` and `LinearMap.mulRight R b` commute, by `LinearMap.commute_mulLeft_right`; this is associativity, $(ax)b = a(xb)$. `LinearMap.pow_mulLeft` says $L_a^n = L_{a^n}$.

The left regular representation is `Algebra.lmul R A`, the algebra homomorphism $A \to \operatorname{End}_R(A)$, $a \mapsto L_a$. It is injective by `Algebra.lmul_injective`, because $L_a(1) = a$. The theorem `Algebra.lmul_isUnit_iff` says that $L_a$ is a unit exactly when $a$ is. Proof: if $a$ has the inverse $b$, then $L_b$ is the inverse of $L_a$. If $L_a$ has the inverse $\phi$, then $\phi$ is $A$-linear for the right action, because $L_a$ commutes with each $R_c$. So $\phi = L_b$ with $b = \phi(1)$, and $ab = 1 = ba$ by injectivity.

#### Epimorphisms of rings

A ring homomorphism $R \to A$ is an epimorphism when two maps $A \to B$ that agree on the image of $R$ are equal. Surjective maps are epimorphisms, but so is $\mathbb{Z} \to \mathbb{Q}$: a ring map from $\mathbb{Q}$ is fixed by its values on $\mathbb{Z}$. The class `Algebra.IsEpi R A` gives the definition used in Mathlib: the multiplication $A \otimes_R A \to A$ is injective, `Algebra.IsEpi.injective_lift_mul`. The theorem `Algebra.isEpi_iff_forall_one_tmul_eq` says that this holds exactly when $1 \otimes a = a \otimes 1$ for each $a \in A$. Proof sketch for a commutative $A$: the elements $1 \otimes a - a \otimes 1$ lie in the kernel of the multiplication and generate it as a left ideal, so the kernel is zero exactly when all of them vanish.

`Algebra.isEpi_of_surjective_algebraMap` covers surjective maps. `Algebra.instIsEpiOfIsDomainOfIsFractionRing` says that a domain maps to its field of fractions by an epimorphism, which generalizes $\mathbb{Z} \to \mathbb{Q}$. For a finite algebra the class says nothing new: `Algebra.isEpi_iff_surjective_algebraMap_of_finite` says that a module-finite epimorphism is surjective. The lemma `Algebra.tmul_comm` is the symmetry $a \otimes b = b \otimes a$ in $A \otimes_R A$ for an epimorphism.

#### Common errors

1. `Module.restrictScalars` is a definition, not an instance. A proof that writes `Module R M` for an $S$-module $M$ fails unless it uses the synonym `RestrictScalars R S M` or adds the structure by `letI`.
2. The isomorphism `AlgEquiv.moduleEndSelf` has the opposite algebra $A^{\mathrm{op}}$ as its source, not $A$. The endomorphisms of $A$ as a left $A$-module are the right multiplications.
3. `IsScalarTower.algebraMap_eq` is stated with `RingHom.comp`. To rewrite a single value, use the pointwise form `IsScalarTower.algebraMap_apply`.

### Exercises

1. (A) Prove that the structure map of `Prod.algebra` sends $r$ to $(\operatorname{algebraMap}(r), \operatorname{algebraMap}(r))$.
2. (A) Show that `AlgHom.restrictScalars R f` and $f$ have the same kernel.
3. (B) Prove that $L_a \circ R_b = R_b \circ L_a$ for all $a, b$ in an associative algebra, and explain why this fails without associativity.
4. (B) Prove that $\mathbb{Z} \to \mathbb{Z}[1/2]$ is an epimorphism of rings, by `Algebra.isEpi_iff_forall_one_tmul_eq`.
5. (B) Show that the opposite of a commutative algebra $A$ is isomorphic to $A$ by `AlgHom.fromOpposite`.
6. (C) Prove that a surjective map $R \to S$ makes the $S$-submodules and the $R$-submodules of an $S$-module the same sets.

### Reference

<?reference?>
