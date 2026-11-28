---
title: Homogeneous and symmetric polynomials
kind: api
modules:
  - Mathlib.RingTheory.MvPolynomial.Homogeneous
  - Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
  - Mathlib.RingTheory.MvPolynomial.EulerIdentity
  - Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
  - Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
  - Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
explains:
  E2: [MvPolynomial.homogeneousSubmodule, MvPolynomial.IsHomogeneous.totalDegree, MvPolynomial.IsHomogeneous.funext, MvPolynomial.weightedHomogeneousComponent, MvPolynomial.IsHomogeneous.sum_X_mul_pderiv, MvPolynomial.symmetricSubalgebra, MvPolynomial.psum, MvPolynomial.esymmAlgHom_fin_bijective, MvPolynomial.mul_esymm_eq_sum]
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

## Homogeneous and symmetric polynomials

### Overview

A polynomial in several variables is homogeneous of degree $n$ when all its monomials have total degree $n$. For example, $x^2 + 3xy - y^2$ is homogeneous of degree $2$, and $x^2 + y$ is not homogeneous. Every polynomial is the sum of its homogeneous components, one for each degree, and the product of two homogeneous polynomials of degrees $m$ and $n$ is homogeneous of degree $m + n$. So the ring $R[x_1, \dots, x_n]$ is a graded ring. If each variable $x_i$ has a weight $w_i$ and the degree of a monomial is the weighted sum of its exponents, the same construction gives the weighted homogeneous polynomials.

A polynomial is symmetric when it does not change under a permutation of the variables. The elementary symmetric polynomials $e_k$ are the sums of all products of $k$ distinct variables, the power sums $p_k$ are $\sum_i x_i^k$, and the complete homogeneous polynomials $h_k$ are the sums of all monomials of degree $k$. The fundamental theorem says that every symmetric polynomial in $n$ variables is a polynomial in $e_1, \dots, e_n$, in exactly one way. The identities of Newton connect the $e_k$ with the $p_k$.

This section is a guide to the six modules on these topics. Section 1 gave the basic definitions `MvPolynomial.IsHomogeneous` and `MvPolynomial.IsSymmetric`. Here the focus is on the gradings, the identity of Euler, the special families of symmetric polynomials and the two main theorems. The evaluation of symmetric polynomials at the roots of a polynomial is in Chapter 5, Section 12.

### The library around it

**Homogeneous polynomials.** The module `Mathlib.RingTheory.MvPolynomial.Homogeneous` states that `φ.IsHomogeneous n` holds when every monomial in the support of $\varphi$ has degree $n$. A nonzero homogeneous polynomial of degree $n$ has total degree $n$, `MvPolynomial.IsHomogeneous.totalDegree`, and coefficients of monomials of other degrees vanish, `MvPolynomial.IsHomogeneous.coeff_eq_zero`. The closure rules are `MvPolynomial.IsHomogeneous.add`, `MvPolynomial.IsHomogeneous.mul`, `MvPolynomial.IsHomogeneous.pow` and `MvPolynomial.IsHomogeneous.prod`, and the basic examples are `MvPolynomial.isHomogeneous_X`, `MvPolynomial.isHomogeneous_C` and `MvPolynomial.isHomogeneous_monomial`. The property passes along ring homomorphisms of the coefficients, `MvPolynomial.IsHomogeneous.map`, and along renaming, `MvPolynomial.IsHomogeneous.rename_isHomogeneous`; for an injective renaming it is an equivalence, `MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff`.

A homogeneous polynomial scales by a power of the scalar,
$$F(c x) = c^d F(x),$$
which is `MvPolynomial.IsHomogeneous.eval_smul`. Over an infinite domain two homogeneous polynomials of the same degree with the same values are equal, `MvPolynomial.IsHomogeneous.funext`. The variant `MvPolynomial.IsHomogeneous.funext_of_le_card` needs only that the degree is at most the cardinality of the domain.

**The grading.** The homogeneous polynomials of degree $n$ form the submodule `MvPolynomial.homogeneousSubmodule σ R n`, with `MvPolynomial.mem_homogeneousSubmodule`. These submodules multiply as the degrees add, `MvPolynomial.homogeneousSubmodule_mul`. The submodule of degree $1$ is spanned by the variables, `MvPolynomial.homogeneousSubmodule_one_eq_span_X`, and its $n$-th power is the submodule of degree $n$, `MvPolynomial.homogeneousSubmodule_one_pow`. For a finite set of variables each of them is finitely generated, `MvPolynomial.homogeneousSubmodule_fg`. The projection to degree $n$ is the linear map `MvPolynomial.homogeneousComponent n`, with the coefficient formula `MvPolynomial.coeff_homogeneousComponent`. The decomposition `MvPolynomial.decomposition` and the instance `MvPolynomial.gradedAlgebra` give the structure of a graded algebra of the library of graded rings. An ideal is homogeneous when it contains the components of its elements, and `MvPolynomial.mem_iff_homogeneousComponent_mem` states the criterion. The module also has `Ideal.mem_span_iff_exists_isHomogeneous`: an element of a ring lies in the ideal generated by a family $x$ exactly when it is the value at $x$ of a homogeneous linear polynomial.

**Weighted homogeneous polynomials.** The module `Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous` takes a weight function $w$ from the variables to an additive monoid $M$. The predicate `MvPolynomial.IsWeightedHomogeneous w φ m` says that every monomial of $\varphi$ has weighted degree $m$. The rules for sums, products and powers are `MvPolynomial.IsWeightedHomogeneous.add`, `MvPolynomial.IsWeightedHomogeneous.mul` and `MvPolynomial.IsWeightedHomogeneous.pow`. The weighted total degree is `MvPolynomial.weightedTotalDegree`, with a variant in `WithBot M`. The components are `MvPolynomial.weightedHomogeneousComponent w m`, which are weighted homogeneous, `MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous`, and which sum to the polynomial, `MvPolynomial.sum_weightedHomogeneousComponent`. The submodules `MvPolynomial.weightedHomogeneousSubmodule` give the graded algebra `MvPolynomial.weightedGradedAlgebra`. With the weight $1$ on each variable the theory is the ordinary one, `MvPolynomial.weightedHomogeneousSubmodule_one` and `MvPolynomial.weightedTotalDegree_one`. Some results need `MvPolynomial.NonTorsionWeight w`: no positive multiple of a weight is $0$. The criterion `MvPolynomial.nonTorsionWeight_of` gives it when all weights are nonzero and $M$ has unique division.

**The identity of Euler.** The module `Mathlib.RingTheory.MvPolynomial.EulerIdentity` proves that for a homogeneous polynomial of degree $n$ in finitely many variables
$$\sum_i x_i \frac{\partial \varphi}{\partial x_i} = n \varphi,$$
which is `MvPolynomial.IsHomogeneous.sum_X_mul_pderiv`. The weighted version is `MvPolynomial.IsWeightedHomogeneous.sum_weight_X_mul_pderiv`. A partial derivative of a homogeneous polynomial of degree $n$ is homogeneous of degree $n - 1$, `MvPolynomial.IsHomogeneous.pderiv`.

**Symmetric polynomials.** The module `Mathlib.RingTheory.MvPolynomial.Symmetric.Defs` defines `φ.IsSymmetric` as invariance under `MvPolynomial.rename e` for every permutation $e$ of the variables. The symmetric polynomials form the subalgebra `MvPolynomial.symmetricSubalgebra σ R`, with `MvPolynomial.mem_symmetricSubalgebra`, and the closure rules are `MvPolynomial.IsSymmetric.add`, `MvPolynomial.IsSymmetric.mul` and `MvPolynomial.IsSymmetric.C`. A bijection of the variables gives an isomorphism of the subalgebras, `MvPolynomial.renameSymmetricSubalgebra`. The module defines four families, each with a lemma of symmetry:

- the elementary symmetric polynomials `MvPolynomial.esymm σ R n`, with `MvPolynomial.esymm_isSymmetric`;
- the complete homogeneous polynomials `MvPolynomial.hsymm σ R n`, with `MvPolynomial.hsymm_isSymmetric`;
- the power sums `MvPolynomial.psum σ R n`, with `MvPolynomial.psum_isSymmetric`;
- the monomial symmetric polynomials `MvPolynomial.msymm σ R μ` for a partition $\mu$, with `MvPolynomial.msymm_isSymmetric`.

For a partition $\mu$ the products `MvPolynomial.esymmPart`, `MvPolynomial.hsymmPart` and `MvPolynomial.psumPart` multiply the members of a family over the parts of $\mu$. The polynomial $e_n$ is the sum of the products over the subsets of size $n$, `MvPolynomial.esymm_eq_sum_subtype`, and it is the elementary symmetric function of the multiset of variables, `MvPolynomial.esymm_eq_multiset_esymm`. Evaluation turns it into the elementary symmetric function `Multiset.esymm` of the values, `MvPolynomial.aeval_esymm_eq_multiset_esymm`.

**The fundamental theorem.** The module `Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem` studies the algebra map
$$R[y_1, \dots, y_n] \to R[x]^{\mathrm{sym}}, \qquad y_i \mapsto e_i,$$
which is `MvPolynomial.esymmAlgHom σ R n`, with `MvPolynomial.esymmAlgHom_apply`. The theorem holds over any commutative ring. For $n$ variables the map is bijective, `MvPolynomial.esymmAlgHom_fin_bijective`. It is surjective when the number of variables is at most $n$, `MvPolynomial.esymmAlgHom_surjective`, and injective when it is at least $n$, `MvPolynomial.esymmAlgHom_injective`. The resulting isomorphism is `MvPolynomial.esymmAlgEquiv`, and its inverse sends $e_{i+1}$ to the variable $y_i$, `MvPolynomial.esymmAlgEquiv_symm_apply`. The proof uses the lexicographic order of monomials: the leading exponent of a symmetric polynomial is antitone, `MvPolynomial.IsSymmetric.antitone_supDegree`, and the leading term of a product of elementary symmetric polynomials is computed with the map `Fin.accumulate`.

**Newton's identities.** The module `Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities` proves, for a finite set of $n$ variables over a commutative ring,
$$\sum_{i + j = n} (-1)^i e_i p_j = 0,$$
which is `MvPolynomial.sum_antidiagonal_card_esymm_psum_eq_zero`. For each $k$ there is a recursive form
$$k e_k = (-1)^{k+1} \sum_{i + j = k,\ i < k} (-1)^i e_i p_j,$$
which is `MvPolynomial.mul_esymm_eq_sum`, and the form `MvPolynomial.psum_eq_mul_esymm_sub_sum` expresses $p_k$ through the $e_i$ and the lower power sums. Over a ring in which $k!$ is invertible, these identities show that the power sums also generate the symmetric polynomials.

#### Common errors

1. `MvPolynomial.IsHomogeneous` counts total degree with weight $1$ on each variable. The zero polynomial is homogeneous of every degree, so `MvPolynomial.IsHomogeneous.totalDegree` needs $\varphi \neq 0$, and `MvPolynomial.IsHomogeneous.inj_right` needs the same hypothesis.
2. The families `MvPolynomial.esymm`, `MvPolynomial.psum` and `MvPolynomial.hsymm` need a `Fintype` instance on the type of variables, because they are finite sums over all variables. A symmetric polynomial in infinitely many variables is legal, but these families do not exist for it.
3. The isomorphism `MvPolynomial.esymmAlgEquiv` sends the variable $y_i$, with $i$ in `Fin n`, to $e_{i+1}$, not to $e_i$. The shift by one comes from the fact that $e_0 = 1$ is not a generator.

### Exercises

1. (A) Write the homogeneous components of $x^3 + 2xy + y^2 + x - 5$, and check that their sum is the polynomial with `MvPolynomial.sum_homogeneousComponent`.
2. (A) Verify the identity of Euler for $\varphi = x^2 y + y^3$ by direct computation, and compare with `MvPolynomial.IsHomogeneous.sum_X_mul_pderiv`.
3. (B) Prove that the product of two nonzero polynomials over a domain is homogeneous only when both factors are homogeneous. Use the components of highest and lowest degree.
4. (B) In three variables, write $x^2 + y^2 + z^2$ and $x^3 + y^3 + z^3$ as polynomials in $e_1, e_2, e_3$, using `MvPolynomial.mul_esymm_eq_sum` or `MvPolynomial.psum_eq_mul_esymm_sub_sum`.
5. (B) Give the weights $w_x = 2$ and $w_y = 3$, and prove that $x^3 - y^2$ is weighted homogeneous of degree $6$. Find all monomials of weighted degree $12$.
6. (C) Let $K$ be a field of characteristic $0$ and $n \ge 1$. Use Newton's identities to prove that the power sums $p_1, \dots, p_n$ generate the algebra of symmetric polynomials in $n$ variables over $K$, and use `MvPolynomial.esymmAlgHom_fin_bijective` to prove that they are algebraically independent.

### Reference

<?reference?>
