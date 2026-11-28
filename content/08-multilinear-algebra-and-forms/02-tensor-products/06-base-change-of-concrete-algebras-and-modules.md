---
title: Base change of concrete algebras and modules
kind: api
modules:
  - Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
  - Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
  - Mathlib.RingTheory.TensorProduct.IsBaseChangePi
  - Mathlib.RingTheory.TensorProduct.IsBaseChangeRightExact
  - Mathlib.RingTheory.TensorProduct.Pi
  - Mathlib.RingTheory.TensorProduct.Quotient
  - Mathlib.RingTheory.TensorProduct.MvPolynomial
  - Mathlib.RingTheory.TensorProduct.MonoidAlgebra
  - Mathlib.RingTheory.TensorProduct.Nontrivial
  - Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
  - Mathlib.RingTheory.PiTensorProduct
explains:
  E2: [IsBaseChange.basis_apply, IsBaseChange.det_endHom, IsBaseChange.directSum, Algebra.TensorProduct.quotIdealMapEquivTensorQuot, MvPolynomial.algebraTensorAlgEquiv, MonoidAlgebra.tensorEquiv_single_tmul_single, PiTensorProduct.tprod_mul_tprod, Algebra.IsEffective.of_section]
  E1: auto
families: []
requires: [V07.C02, V07.C03, V06.C02, V06.C05, V06.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Base change of concrete algebras and modules

### Overview

Section 4 defines the base change $S \otimes_R M$ and the predicate `IsBaseChange`, and proves the universal property. In practice a proof needs to know what the base change of a given object is. The base change of $R[x, y]$ to $S$ is $S[x, y]$. The base change of $R/I$ is $S/I S$. The base change of a free module is free with the same basis, and the base change of a matrix is the same matrix with its entries mapped to $S$. This section collects these computations.

The results come in two forms. Some are equivalences of algebras with an explicit tensor product, such as $A \otimes_R R[\sigma] \cong A[\sigma]$ for polynomial rings. Others are stated with `IsBaseChange`, so that a localization or any other model of the base change can be used in place of the tensor product. The section ends with the tensor product of a whole family of algebras, the algebra $\bigotimes_i A_i$, and with the map $s \mapsto s \otimes 1 - 1 \otimes s$, which detects the elements of $S$ that come from $R$.

The section uses Section 4 throughout, bases and matrices from Volume 7, ideals and quotients from Volume 6, Chapter 2, and polynomial rings from Volume 6, Chapter 5.

### The library around it

#### Bases, linear maps and determinants

Fix a commutative ring $R$, a commutative $R$-algebra $S$, and an $R$-linear map $\varepsilon : V \to W$ to an $S$-module $W$ with `IsBaseChange S ε`. The module `Mathlib.RingTheory.TensorProduct.IsBaseChangeFree` transports bases.

**Theorem.** If $(b_i)_{i \in I}$ is a basis of $V$, then $(\varepsilon(b_i))_{i \in I}$ is a basis of the $S$-module $W$. The coordinates of $\varepsilon(v)$ are the images in $S$ of the coordinates of $v$.

*Proof.* The basis is an isomorphism $V \cong R^{(I)}$. Base change preserves isomorphisms and direct sums, so $W \cong S \otimes_R V \cong S \otimes_R R^{(I)} \cong S^{(I)}$. Follow $b_i$ through these maps: $b_i \mapsto 1 \otimes e_i \mapsto e_i$. So $\varepsilon(b_i)$ corresponds to the basis vector $e_i$ of $S^{(I)}$. For $v = \sum_i r_i b_i$, $\varepsilon(v) = \sum_i \varphi(r_i) \varepsilon(b_i)$, where $\varphi : R \to S$ is the structure map. $\square$

The basis is `IsBaseChange.basis`, with `IsBaseChange.basis_apply` for $\varepsilon(b_i)$ and `IsBaseChange.basis_repr_comp_apply` for the coordinates. The corollary `IsBaseChange.free` says that a base change of a free module is free. In the other direction, let $R$ be an algebra over a smaller ring $A$ and let $b$ be a basis of an $R$-module $V$. Then `IsBaseChange.of_basis` says that $V$ is the base change of $A^{(I)}$ to $R$ along the map `Finsupp.linearCombination A b`, which sends $e_i$ to $b_i$.

The module `Mathlib.RingTheory.TensorProduct.IsBaseChangeHom` treats modules of linear maps. Let $M$ be finite and free over $R$. If $P$ is a base change of $N$, then $\operatorname{Hom}_R(M, P)$ is a base change of $\operatorname{Hom}_R(M, N)$ (`IsBaseChange.linearMapRight`). If $P$ is a base change of $M$ and $Q$ is a base change of $N$, then $\operatorname{Hom}_S(P, Q)$ is a base change of $\operatorname{Hom}_R(M, N)$ (`IsBaseChange.linearMapLeftRight`), through the map `IsBaseChange.linearMapLeftRightHom` that sends $f$ to its base change. The case $N = M$ is `IsBaseChange.end`, with the map `IsBaseChange.endHom` of endomorphisms; it satisfies `IsBaseChange.endHom_comp_apply`: $f_S(\varepsilon(m)) = \varepsilon(f(m))$. The finiteness hypothesis is needed. For $M = \mathbb{Z}^{(\mathbb{N})}$, $N = \mathbb{Z}$ and $S = \mathbb{Q}$, the module $\operatorname{Hom}(M, \mathbb{Z})$ is $\mathbb{Z}^{\mathbb{N}}$, and the map $\mathbb{Q} \otimes \mathbb{Z}^{\mathbb{N}} \to \mathbb{Q}^{\mathbb{N}}$ is not surjective: the elements of the image have bounded denominators, and the sequence $(1/n)_n$ does not.

**Theorem.** Let $M$ be finite free with a base change $P$, and let $f$ be an endomorphism of $M$. Then $\det(f_S) = \varphi(\det f)$.

*Proof.* Choose a basis $b$ of $M$, and take the basis $\varepsilon(b)$ of $P$ of the first theorem. By `IsBaseChange.endHom_toMatrix`, the matrix of $f_S$ in this basis is the matrix of $f$ with $\varphi$ applied to each entry. The determinant is a polynomial in the entries with integer coefficients, so it commutes with the ring map $\varphi$. $\square$

This is `IsBaseChange.det_endHom`, stated with `LinearMap.det`. The same rule for matrices of maps between two modules is `IsBaseChange.linearMapLeftRightHom_toMatrix`.

#### Products, direct sums and exact sequences

The module `Mathlib.RingTheory.TensorProduct.IsBaseChangePi` shows that base change commutes with finite products and with all direct sums.

| Lean name | Statement |
|---|---|
| `IsBaseChange.prodMap` | if $f$ and $g$ are base changes, so is $f \times g : M \times N \to M' \times N'$ |
| `IsBaseChange.pi` | the same for a finite product $\prod_i M_i \to \prod_i M'_i$ |
| `IsBaseChange.finitePow` | the same for $M^\iota \to M'^\iota$ with $\iota$ finite |
| `IsBaseChange.directSum` | if each $\varepsilon_i$ is a base change, so is $\bigoplus_i \varepsilon_i$, for any index set |
| `IsBaseChange.finsuppPow` | the same for $M^{(\iota)} \to M'^{(\iota)}$ |

The proof of `IsBaseChange.directSum` is the isomorphism $S \otimes \bigoplus_i N_i \cong \bigoplus_i S \otimes N_i$ of Section 2, followed by the isomorphisms $S \otimes N_i \cong N'_i$ given by the hypotheses. The finiteness in `IsBaseChange.pi` is needed, because the tensor product does not commute with infinite products. The instances `IsLocalizedModule.prodMap` and `IsLocalizedModule.pi` of the same module give the special case of a localization.

The module `Mathlib.RingTheory.TensorProduct.IsBaseChangeRightExact` has one result, `IsBaseChange.of_right_exact`. It takes a commutative diagram with exact rows $M_1 \to M_2 \to M_3 \to 0$ over $R$ and $N_1 \to N_2 \to N_3 \to 0$ over $S$, and vertical maps $h_1, h_2, h_3$. If $h_1$ and $h_2$ are base changes, then $h_3$ is a base change. The proof is the right exactness of Section 2: $S \otimes M_3$ is the cokernel of $S \otimes M_1 \to S \otimes M_2$, and $N_3$ is the cokernel of the isomorphic map $N_1 \to N_2$.

#### Products and quotients of algebras

The module `Mathlib.RingTheory.TensorProduct.Pi` upgrades the linear isomorphisms of Section 2 to algebras. For an $R$-algebra $A$ and a finite family of $R$-algebras $B_i$, the algebra equivalence `Algebra.TensorProduct.piRight` is

$$A \otimes_R \prod_i B_i \;\cong\; \prod_i (A \otimes_R B_i), \qquad a \otimes (b_i)_i \mapsto (a \otimes b_i)_i,$$

with `Algebra.TensorProduct.piRight_tmul`. Without finiteness only the algebra map `Algebra.TensorProduct.piRightHom` remains. The binary case is `Algebra.TensorProduct.prodRight`, and the case $B_i = R$ is `Algebra.TensorProduct.piScalarRight`: $A \otimes_R R^\iota \cong A^\iota$.

The module `Mathlib.RingTheory.TensorProduct.Quotient` computes the base change of a quotient ring.

**Theorem.** Let $A \to B$ be a map of commutative rings and let $I$ be an ideal of $A$. Then $B / I B \cong B \otimes_A A/I$ as $B$-algebras, by $b \mapsto b \otimes 1$.

*Proof.* The sequence $I \to A \to A/I \to 0$ is exact. By right exactness, so is $B \otimes_A I \to B \otimes_A A \to B \otimes_A A/I \to 0$. Under $B \otimes_A A \cong B$, the image of $B \otimes_A I$ is the set of sums $\sum_k b_k a_k$ with $a_k \in I$, which is the ideal $I B$. So $B \otimes_A A/I \cong B / I B$ as $B$-modules. The map $b \mapsto b \otimes 1$ is multiplicative, so this is an isomorphism of algebras. $\square$

This is `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`, where $I B$ is written `I.map (algebraMap A B)`. The value on a class is `Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk`. The version with $A/I$ on the left is `Algebra.TensorProduct.quotIdealMapEquivQuotTensor`. For two algebras $A$ and $T$ over $R$ and an ideal $I$ of $T$, `Algebra.TensorProduct.tensorQuotientEquiv` gives $A \otimes_R T/I \cong (A \otimes_R T)/I (A \otimes_R T)$, and `Algebra.TensorProduct.quotientTensorEquiv` does the same for an ideal of the left factor. The module version of the key step is `Ideal.subtype_rTensor_range`: the image of $I \otimes M$ in $M$ is $I M$. Finally `Algebra.tensorQuotientTensorEquiv` treats the quotient of a base change by one element and its further base change.

#### Polynomial rings and monoid algebras

A monoid algebra $B[M]$ is the free $B$-module on $M$ with the product of $M$. The module `Mathlib.RingTheory.TensorProduct.MonoidAlgebra` proves that the construction commutes with the tensor product.

| Lean name | Statement |
|---|---|
| `MonoidAlgebra.rTensorEquivAlgEquiv` | $A \otimes_R B[M] \cong (A \otimes_R B)[M]$ |
| `MonoidAlgebra.lTensorAlgEquiv` | $A[M] \otimes_R B \cong (A \otimes_R B)[M]$ |
| `MonoidAlgebra.scalarTensorEquiv` | $A \otimes_R R[M] \cong A[M]$ |
| `MonoidAlgebra.tensorEquiv` | $R[M] \otimes_R R[N] \cong R[M \times N]$, as modules |

The proof of the first line: as a module, $B[M] = \bigoplus_{m \in M} B$, and the tensor product commutes with direct sums. The isomorphism sends $a \otimes b\,m$ to $(a \otimes b)\,m$. It is multiplicative on these generators, because $(a \otimes b\, m)(a' \otimes b'\, m') = a a' \otimes b b'\, m m'$ on both sides. For the last line, `MonoidAlgebra.tensorEquiv_single_tmul_single` says that $r_1 m \otimes r_2 n \mapsto r_1 r_2 (m, n)$. Each result has a copy for the additive version `AddMonoidAlgebra`, such as `AddMonoidAlgebra.scalarTensorEquiv`. The instance `MonoidAlgebra.instIsPushout` says that $B[M]$ is a pushout of $A[M]$ whenever $B$ is a pushout of $A$, in the sense of `Algebra.IsPushout`.

Multivariable polynomials are the case $M = \sigma \to_0 \mathbb{N}$, and the module `Mathlib.RingTheory.TensorProduct.MvPolynomial` specializes the results.

**Theorem.** For an $R$-algebra $A$, $A \otimes_R R[\sigma] \cong A[\sigma]$ as $A$-algebras, by $a \otimes p \mapsto a \cdot \bar p$, where $\bar p$ is $p$ with its coefficients mapped to $A$.

*Proof.* Both sides are free $A$-modules on the monomials $x^d$, $d \in \sigma \to_0 \mathbb{N}$: the left side by the basis theorem of Section 4, the right side by definition. The map sends the basis vector $1 \otimes x^d$ to $x^d$, so it is bijective. It sends $(a \otimes x^d)(a' \otimes x^{d'}) = a a' \otimes x^{d + d'}$ to $a a' x^{d + d'}$, the product of the images, so it is multiplicative. $\square$

This is `MvPolynomial.algebraTensorAlgEquiv`, with `MvPolynomial.algebraTensorAlgEquiv_tmul` for the formula. The general form `MvPolynomial.rTensorAlgEquiv` is $S \otimes_R N[\sigma] \cong (S \otimes_R N)[\sigma]$, with `MvPolynomial.coeff_rTensorAlgEquiv_tmul`: the coefficient of $x^d$ in the image of $s \otimes p$ is $s \otimes p_d$. The equivalence `MvPolynomial.scalarRTensorAlgEquiv` is the case $N = R$. The equivalence `MvPolynomial.tensorEquivSum` is $S[\sigma] \otimes_R R[\iota] \cong S[\sigma \sqcup \iota]$, so polynomial rings in disjoint sets of variables multiply as expected. The lemma `MvPolynomial.aeval_one_tmul` says that evaluation commutes with $s \mapsto 1 \otimes s$.

#### When is $A \otimes_R B$ nonzero

The tensor product of two nonzero algebras can be zero: $\mathbb{Z}/2 \otimes_{\mathbb{Z}} \mathbb{Z}/3 = 0$. The module `Mathlib.RingTheory.TensorProduct.Nontrivial` gives a sufficient condition. The theorem `Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain` says: if $A$ and $B$ are domains and both structure maps $R \to A$ and $R \to B$ are injective, then $A \otimes_R B$ is nonzero. The section states this result without a proof.

#### The map $s \mapsto s \otimes 1 - 1 \otimes s$

For an $R$-algebra $S$, the module `Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight` defines the $R$-linear map `Algebra.TensorProduct.includeLeftSubRight`, here written $\delta$:

$$\delta : S \to S \otimes_R S, \qquad \delta(s) = s \otimes 1 - 1 \otimes s.$$

Each element $\varphi(r)$ of the image of $R$ satisfies $\delta(\varphi(r)) = r(1 \otimes 1) - r (1 \otimes 1) = 0$ (`Algebra.TensorProduct.includeLeftSubRight_algebraMap_zero`). The algebra is *effective*, `Algebra.IsEffective R S`, when the converse holds: the sequence $R \to S \xrightarrow{\delta} S \otimes_R S$ is exact (`Function.Exact`). Then the elements of $S$ with $s \otimes 1 = 1 \otimes s$ are exactly those that come from $R$ (`Algebra.IsEffective.eqLocus_includeLeft_includeRight`).

**Theorem.** If there is an $R$-algebra map $g : S \to R$, then $S$ is effective over $R$.

*Proof.* Let $s \in S$ with $s \otimes 1 = 1 \otimes s$. Apply the map $g \otimes \mathrm{id} : S \otimes_R S \to R \otimes_R S \cong S$, which sends $x \otimes y$ to $g(x) y$. The left side gives $g(s) \cdot 1 = \varphi(g(s))$, and the right side gives $g(1) s = s$. So $s = \varphi(g(s))$ comes from $R$. $\square$

This is `Algebra.IsEffective.of_section`. The main result is `Algebra.IsEffective.of_faithfullyFlat`: a faithfully flat algebra is effective. The proof base changes along $R \to S$ itself, where the multiplication $S \otimes_R S \to S$ is a section, and descends the exactness with `Algebra.IsEffective.of_isEffective_tensorProduct_of_faithfullyFlat`. In the language of categories, `Algebra.codRestrictEqLocusPushoutCocone.bijective_of_faithfullyFlat` says that $R$ is the equalizer of the two maps $S \rightrightarrows S \otimes_R S$ in the category of commutative rings. This is the first step of faithfully flat descent.

#### The tensor product of a family of algebras

Chapter 3 builds the tensor product $\bigotimes_i A_i$ of a family of modules, with the pure tensors $\otimes_i a_i$ given by `PiTensorProduct.tprod`. The module `Mathlib.RingTheory.PiTensorProduct` makes it an algebra when each $A_i$ is an $R$-algebra. The unit is $\otimes_i 1$ (`PiTensorProduct.one_def`), and the product is the bilinear map `PiTensorProduct.mul` with

$$\Big(\bigotimes_i a_i\Big)\Big(\bigotimes_i b_i\Big) = \bigotimes_i a_i b_i.$$

This is `PiTensorProduct.tprod_mul_tprod`. It is a definition on generators, so the work is to show that the product exists, and this is the same argument as for two algebras in Section 4. The instances give a semiring, a ring, a commutative ring when each $A_i$ is commutative (`PiTensorProduct.instCommRing`), and an algebra over $R$ with `PiTensorProduct.algebraMap_apply`.

The inclusion of one factor is `PiTensorProduct.singleAlgHom i`, which sends $a$ to the pure tensor with $a$ at the place $i$ and $1$ elsewhere. Algebra maps out of $\bigotimes_i A_i$ are built by `PiTensorProduct.liftAlgHom` from a multilinear map that preserves $1$ and products, and two algebra maps are equal when they agree on each factor (`PiTensorProduct.algHom_ext`, for a finite index set). The equivalence `PiTensorProduct.constantBaseRingEquiv` identifies $\bigotimes_{i \in \iota} R$ with $R$, by $\otimes_i r_i \mapsto \prod_i r_i$. The monoid map `PiTensorProduct.tprodMonoidHom` records that $(a_i)_i \mapsto \otimes_i a_i$ is multiplicative.

#### Common errors

1. Expecting `IsBaseChange.linearMapRight` or `IsBaseChange.end` without a finiteness hypothesis. The module $\operatorname{Hom}_R(M, N)$ commutes with base change only when $M$ is finite and free, or under similar conditions. The hypotheses are instance arguments `Module.Free R M` and `Module.Finite R M`, and a missing instance gives an error about instance synthesis, not about the statement.
2. Using `Algebra.TensorProduct.piRight` for an infinite family. The tensor product does not commute with infinite products, and the library has only `Algebra.TensorProduct.piRightHom` in that case.
3. Reading $\delta(s) = 0$ as $s \in R$ for every algebra. This is the definition of `Algebra.IsEffective`, and it needs a proof, such as faithful flatness or a section.

### Exercises

1. (A) Use `MvPolynomial.algebraTensorAlgEquiv` to show that $\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R}[x, y] \cong \mathbb{C}[x, y]$ as $\mathbb{C}$-algebras.
2. (A) Compute $\mathbb{Z}/5 \otimes_{\mathbb{Z}} \mathbb{Z}[i]$ as a ring. Hint: $\mathbb{Z}[i] \cong \mathbb{Z}[x]/(x^2 + 1)$, and $x^2 + 1$ has two roots in $\mathbb{F}_5$.
3. (B) Show that $R[M] \otimes_R R[N] \cong R[M \times N]$ is multiplicative, and deduce $R[x] \otimes_R R[y] \cong R[x, y]$ from the case $M = N = \mathbb{N}$.
4. (B) Let $f$ be the endomorphism of $\mathbb{Z}^2$ with matrix $\begin{pmatrix} 2 & 1 \\ 0 & 3 \end{pmatrix}$. Compute $\det(f_S)$ for $S = \mathbb{Z}/6$, and decide whether $f_S$ is invertible.
5. (B) Show that $\mathbb{Q} \to \mathbb{Q}[x]$ is effective, first with a section and then directly with the basis $x^i \otimes x^j$ of $\mathbb{Q}[x] \otimes \mathbb{Q}[x]$.
6. (C) Show that $\mathbb{Z} \to \mathbb{Z} \times \mathbb{Z}/2$ is not faithfully flat but is effective. Hint: the projection to the first factor is a section.

### Reference

<?reference?>
