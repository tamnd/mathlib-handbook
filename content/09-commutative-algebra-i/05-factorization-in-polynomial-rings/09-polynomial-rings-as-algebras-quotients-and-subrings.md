---
title: Polynomial rings as algebras, quotients and subrings
kind: api
modules:
  - Mathlib.RingTheory.PolynomialAlgebra
  - Mathlib.RingTheory.MatrixPolynomialAlgebra
  - Mathlib.RingTheory.Polynomial.Opposites
  - Mathlib.RingTheory.Polynomial.Quotient
  - Mathlib.RingTheory.Polynomial.Ideal
  - Mathlib.RingTheory.Polynomial.Tower
  - Mathlib.RingTheory.Polynomial.Subring
  - Mathlib.RingTheory.Polynomial.IsIntegral
explains:
  E2: [polyEquivTensor, matPolyEquiv, Polynomial.opRingEquiv, Ideal.polynomialQuotientEquivQuotientPolynomial, Polynomial.quotientSpanXSubCAlgEquiv, Polynomial.ker_evalRingHom, Polynomial.isIntegral_iff_isIntegral_coeff]
  E1: auto
families: []
requires: [V06.C05, V07.C03, V08.C02, V09.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Polynomial rings as algebras, quotients and subrings

### Overview

A ring of polynomials $A[X]$ is related to other rings by a set of standard isomorphisms. If $A$ is an algebra over $R$, then $A[X]$ is the tensor product $A \otimes_R R[X]$. A matrix of polynomials is a polynomial with matrix coefficients, $M_n(R[X]) \cong M_n(R)[X]$. The quotient of $R[X]$ by the extension of an ideal $I$ of $R$ is the ring $(R/I)[X]$. The quotient of $R[X]$ by $X - a$ is $R$ itself, through evaluation at $a$.

Mathematics uses these identifications without comment. In the library each one is a named equivalence, and a proof must apply it explicitly. This section is a guide to the modules that hold them, and to the modules on polynomials over a subring, on polynomials in a tower of algebras, and on integrality of coefficients. A proof that crosses one of these identifications usually has two steps: apply the equivalence, then simplify with the lemmas that compute it on constants, on $X$ and on coefficients. The modules give such lemmas next to each equivalence, and the paragraphs below name the main ones.

### The library around it

**Polynomials as a tensor product.** The module `Mathlib.RingTheory.PolynomialAlgebra` first gives the instance `Polynomial.algebra`: if $A$ is an $R$-algebra, then so is $A[X]$, with `Polynomial.algebraMap_def` to unfold its structure map. The main equivalence is
$$A[X] \cong A \otimes_R R[X],$$
which is `polyEquivTensor R A`, an isomorphism of $R$-algebras. On a pure tensor it is given by `polyEquivTensor_symm_apply_tmul`: the tensor $a \otimes p$ goes to $a$ times the image of $p$ in $A[X]$. When $A$ is commutative, `polyEquivTensor'` is the same map as an isomorphism of $A$-algebras. The instance `instIsPushoutPolynomial` states the same fact in the language of pushouts: for an $R$-algebra $S$, the square formed by $R$, $S$, $R[X]$ and $S[X]$ satisfies `Algebra.IsPushout`. With this instance, results about base change apply to polynomial rings directly. The auxiliary namespace PolyEquivTensor holds the pieces of the construction, and a user rarely needs them.

**Matrices of polynomials.** The module `Mathlib.RingTheory.MatrixPolynomialAlgebra` proves
$$M_n(R[X]) \cong M_n(R)[X],$$
which is `matPolyEquiv`, an isomorphism of $R$-algebras. The coefficient of $X^k$ in the image of a matrix $m$ is the matrix of the coefficients of $X^k$ in the entries, `matPolyEquiv_coeff_apply`. This identification is the main step in the proof of the theorem of Cayley and Hamilton in Volume 7. Evaluation commutes with it, `matPolyEquiv_eval`. The lemma `eval_det_add_X_smul` says that the constant term of $\det(A + X M)$ depends only on $A$. For a ring homomorphism $f : R \to A$, `RingHom.polyToMatrix` sends a polynomial over $R$ to a matrix of polynomials over $A$.

**Opposite rings.** The module `Mathlib.RingTheory.Polynomial.Opposites` gives `Polynomial.opRingEquiv R`, a ring isomorphism between $(R[X])^{\mathrm{op}}$ and $R^{\mathrm{op}}[X]$. It keeps coefficients, `Polynomial.coeff_opRingEquiv`, and degrees, `Polynomial.natDegree_opRingEquiv`. The equivalence is used to transfer statements between left and right versions. For example, `Polynomial.isDomain_iff` says that $R[X]$ is a domain exactly when $R$ is a domain with cancellative addition, and `Polynomial.isLeftCancelMulZero_iff` and `Polynomial.isRightCancelMulZero_iff` give the one-sided versions for a noncommutative semiring $R$.

**Quotients of polynomial rings.** The module `Mathlib.RingTheory.Polynomial.Quotient` holds the quotient isomorphisms. Evaluation at $a$ gives
$$R[X] / (X - a) \cong R,$$
which is `Polynomial.quotientSpanXSubCAlgEquiv a`, an isomorphism of $R$-algebras. The variant `Polynomial.quotientSpanCXSubCAlgEquiv x y` divides by $x$ and by $X - y$ and gives $R / (x)$, and `Polynomial.quotientSpanCXSubCXSubCAlgEquiv` does the same in two variables. For an ideal $I$ of $R$,
$$(R / I)[X] \cong R[X] / I R[X],$$
which is `Ideal.polynomialQuotientEquivQuotientPolynomial I`. The version for several variables is `MvPolynomial.quotientEquivQuotientMvPolynomial`. It follows that the extension of a prime ideal is prime, `Ideal.isDomain_map_C_quotient`. The lemma `Polynomial.modByMonic_eq_zero_iff_quotient_eq_zero` connects division by a monic polynomial $q$ with the quotient by $(q)$. Finally, `Ideal.IsField.of_isPrincipalIdealRing_polynomial` says that if $R$ is a domain and $R[X]$ is a principal ideal ring, then $R$ is a field. The reason is that the ideal $(a, X)$ is principal only when $a = 0$ or $a$ is a unit.

**Kernels.** The module `Mathlib.RingTheory.Polynomial.Ideal` computes kernels. The kernel of evaluation at $a$ is the ideal generated by $X - a$, `Polynomial.ker_evalRingHom`, and the kernel of the constant coefficient is the ideal generated by $X$, `Polynomial.ker_constantCoeff`. For a monic $q$, the kernel of the map $p \mapsto p \bmod q$ is the ideal $(q)$, `Polynomial.ker_modByMonicHom`. The lemma `Polynomial.mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero` describes the ideal of a point in two variables.

**Towers.** The module `Mathlib.RingTheory.Polynomial.Tower` treats a tower $R \to A \to B$ of algebras. A polynomial over $R$ can be evaluated in $B$ directly, or first mapped to $A$. The lemma `Polynomial.aeval_map_algebraMap` says that the two give the same result. The lemma `Polynomial.aeval_algebraMap_eq_zero_iff` says that an element $x$ of $A$ is a root of $p$ exactly when its image in $B$ is a root, under a hypothesis of injectivity. The version with an explicit injectivity hypothesis is `Polynomial.aeval_algebraMap_eq_zero_iff_of_injective`.

**Subrings.** The module `Mathlib.RingTheory.Polynomial.Subring` moves polynomials between a ring $R$ and a subring $T$. If all coefficients of $p$ lie in $T$, then `Polynomial.toSubring p T hp` is $p$ as a polynomial over $T$. It keeps the degree, `Polynomial.degree_toSubring`, and the property of being monic, `Polynomial.monic_toSubring`. In the other direction, `Polynomial.ofSubring T p` is a polynomial over $R$ whose coefficients lie in $T$, `Polynomial.coeffs_ofSubring`.

**Integrality of coefficients.** The module `Mathlib.RingTheory.Polynomial.IsIntegral` proves that a polynomial over an $R$-algebra $S$ is integral over $R[X]$ exactly when all its coefficients are integral over $R$:
$$f \text{ integral over } R[X] \iff f_n \text{ integral over } R \text{ for all } n,$$
which is `Polynomial.isIntegral_iff_isIntegral_coeff`, with the multivariate version `MvPolynomial.isIntegral_iff_isIntegral_coeff`. A monic factor of a monic polynomial has integral coefficients, `Polynomial.isIntegral_coeff_of_dvd`. As a result, the polynomial ring over an integrally closed domain is integrally closed, the instance `instIsIntegrallyClosedPolynomialOfIsDomain`.

#### Common errors

1. The quotient isomorphisms have similar names. The name `Polynomial.quotientSpanXSubCAlgEquiv` divides by $X - a$ only, and the name with CXSubC divides by a constant and by $X - y$. Read the type before use.
2. The equivalence `polyEquivTensor R A` puts $A$ on the left of the tensor product. A proof that needs $R[X] \otimes_R A$ must compose it with the commutativity of the tensor product.
3. `Polynomial.toSubring` takes a proof that the coefficients lie in the subring. A goal about `p.toSubring T hp` often needs `Polynomial.coeff_toSubring` to remove the subring before simp can work.

### Exercises

1. (A) Use `Polynomial.ker_evalRingHom` to prove that the ideal $(X - a)$ of $R[X]$ is prime when $R$ is a domain, and maximal when $R$ is a field.
2. (A) Use `Ideal.polynomialQuotientEquivQuotientPolynomial` to prove that $\mathbb{Z}[X] / (p)$ is a domain for a prime number $p$, and that the ideal $(p, X)$ is maximal.
3. (B) Prove `Ideal.IsField.of_isPrincipalIdealRing_polynomial` for the ring $\mathbb{Z}$: show that the ideal $(2, X)$ of $\mathbb{Z}[X]$ is not principal.
4. (B) Let $m \in M_2(\mathbb{Z}[X])$ have entries $X$, $1$, $0$ and $X^2$. Compute the image of $m$ under `matPolyEquiv` as a polynomial with coefficients in $M_2(\mathbb{Z})$.
5. (B) Let $S$ be a commutative $R$-algebra. Use `polyEquivTensor'` to give an isomorphism of $S$-algebras between $S[X]$ and $S \otimes_R R[X]$, and compute the image of $s X^2 + 1$.
6. (C) Let $S$ be an $R$-algebra. Use `Polynomial.isIntegral_coeff_of_dvd` to prove that every monic factor in $S[X]$ of a monic polynomial in $R[X]$ has coefficients that are integral over $R$. Deduce that if $R$ is integrally closed in a domain $S$, then each such factor comes from $R[X]$.

### Reference

<?reference?>
