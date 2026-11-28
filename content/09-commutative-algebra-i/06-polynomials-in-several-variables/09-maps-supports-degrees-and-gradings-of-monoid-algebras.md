---
title: Maps, supports, degrees and gradings of monoid algebras
kind: api
modules:
  - Mathlib.Algebra.MonoidAlgebra.MapDomain
  - Mathlib.Algebra.MonoidAlgebra.Module
  - Mathlib.Algebra.MonoidAlgebra.Support
  - Mathlib.Algebra.MonoidAlgebra.Degree
  - Mathlib.Algebra.MonoidAlgebra.Division
  - Mathlib.Algebra.MonoidAlgebra.Grading
  - Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
  - Mathlib.Algebra.MonoidAlgebra.Ideal
  - Mathlib.Algebra.MonoidAlgebra.ToDirectSum
explains:
  E2: [MonoidAlgebra.mapDomain_mul, MonoidAlgebra.mapDomain_comapDomain, MonoidAlgebra.supported_eq_span_single, MonoidAlgebra.support_coeff_mul_subset, AddMonoidAlgebra.supDegree_add_le, AddMonoidAlgebra.coeff_supDegree_add_supDegree, AddMonoidAlgebra.divOf_add_modOf, AddMonoidAlgebra.grade.isInternal, MonoidAlgebra.coeff_mul_mul_of_uniqueMul, MonoidAlgebra.mem_ideal_span_of_image]
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

## Maps, supports, degrees and gradings of monoid algebras

### Overview

Section 8 defined the monoid algebra $R[M]$ and its universal property. This section covers the files that use the structure of $M$ and of $R$ more closely. A map $M \to N$ or $R \to S$ gives a map of monoid algebras. The module structure gives a basis indexed by $M$. The support of a product lies in the product of the supports. A degree function on $M$ gives a degree and a leading coefficient on $R[M]$. Division by a monomial, gradings by $M$, a criterion for the absence of zero divisors, ideals spanned by monomials and the identification with direct sums complete the list.

Most of these files are written for the additive version `AddMonoidAlgebra R M`, because polynomials need them. The degree of a polynomial in one variable, the total degree of a polynomial in several variables, and weighted degrees are all cases of `AddMonoidAlgebra.supDegree`. The division `MvPolynomial.divMonomial` of Section 6 is a case of `AddMonoidAlgebra.divOf`. So a reader who knows this section knows where many polynomial lemmas come from.

### The library around it

#### Maps of the monoid and of the coefficients

The file `Mathlib.Algebra.MonoidAlgebra.MapDomain` has two kinds of maps. For a function $f \colon M \to N$, `MonoidAlgebra.mapDomain` $f$ sends $\sum r_m \, m$ to $\sum r_m \, f(m)$. On single elements it is `MonoidAlgebra.mapDomain_single`: $r \, m \mapsto r \, f(m)$. Several terms can have the same image, and then their coefficients add. For an additive map $f \colon R \to S$, `MonoidAlgebra.map` $f$ applies $f$ to each coefficient (`MonoidAlgebra.map_single`).

The map along the monoid respects products when $f$ does. This is `MonoidAlgebra.mapDomain_mul`: for a multiplicative $f$, $\operatorname{mapDomain} f (xy) = \operatorname{mapDomain} f (x) \operatorname{mapDomain} f (y)$. Proof: both sides are biadditive in $(x, y)$, so it is enough to check single elements. Then the left side is $(r_1 r_2) \, f(m_1 m_2)$ and the right side is $(r_1 r_2) \, f(m_1) f(m_2)$, which agree. The bundled forms follow the usual pattern of names.

| Lean name | Statement |
| --- | --- |
| `MonoidAlgebra.mapDomainRingHom` | a monoid map $M \to N$ gives a ring map $R[M] \to R[N]$ |
| `MonoidAlgebra.mapDomainNonUnitalRingHom` | the same for a multiplicative map of magmas |
| `MonoidAlgebra.mapDomainRingEquiv` | a monoid isomorphism gives a ring isomorphism |
| `MonoidAlgebra.mapDomainAddEquiv` | a bijection $M \cong N$ gives an additive isomorphism |
| `MonoidAlgebra.mapRingHom` | a ring map $R \to S$ gives a ring map $R[M] \to S[M]$ |
| `MonoidAlgebra.mapRingEquiv` | a ring isomorphism $R \cong S$ gives $R[M] \cong S[M]$ |
| `MonoidAlgebra.commRingEquiv` | $R[M][N] \cong R[N][M]$ |
| `MonoidAlgebra.toAdditive` | $R[M] \cong R[\text{Additive } M]$ as rings |
| `AddMonoidAlgebra.toMultiplicative` | $R[M] \cong R[\text{Multiplicative } M]$ as rings |

The algebra versions of these maps are in `Mathlib.Algebra.MonoidAlgebra.Basic` and appear in Section 8.

For an injective $f \colon M \to N$ there is a map back. `MonoidAlgebra.comapDomain` $f$ keeps the coefficients of $x \in R[N]$ at the points of the image of $f$ and reads them on $M$. The lemma `MonoidAlgebra.mapDomain_comapDomain` says that `mapDomain` $f$ undoes it when the support of $x$ lies in the range of $f$. Proof: compare the coefficients at $n \in N$. If $n = f(m)$, the left side has coefficient $x(f(m))$, because $f$ is injective and only $m$ maps to $n$. If $n$ is not in the range, both sides are zero, the right side because the support of $x$ lies in the range.

#### The module structure

The file `Mathlib.Algebra.MonoidAlgebra.Module` gives `MonoidAlgebra S M` the structure of an $R$-module for each $R$-module $S$ (`MonoidAlgebra.instModule`), with the scalar product on the coefficients. The map `MonoidAlgebra.lsingle` $m$ is the linear map $s \mapsto s \, m$, and `MonoidAlgebra.coeffLinearEquiv` is the linear form of the equivalence with `M →₀ S`. The basis `MonoidAlgebra.basis` of $k[M]$ over $k$ is indexed by $M$, and `MonoidAlgebra.basis_apply` says that its vector at $m$ is $1 \, m$. So $k[M]$ is a free $k$-module of rank $\#M$.

For a set $s \subseteq M$, `MonoidAlgebra.supported` is the submodule of elements with support in $s$. The equivalence `MonoidAlgebra.supportedEquivFinsupp` identifies it with `s →₀ S`. The lemma `MonoidAlgebra.supported_eq_span_single` says that it is the span of the elements $1 \, m$ with $m \in s$. Proof: each element of the span is a finite sum $\sum r_m \, m$ with $m \in s$, so its support lies in $s$. Conversely, an element with support in $s$ is the sum of its terms $r_m \, m = r_m \cdot (1 \, m)$, by `MonoidAlgebra.sum_coeff_single`. The lemma `MonoidAlgebra.of_mem_span_of_iff` says that $1 \, m$ lies in the span of the elements $1 \, m'$ with $m' \in s$ only when $m \in s$, over a nontrivial ring. The maps `MonoidAlgebra.mapDomainLinearMap` and `MonoidAlgebra.mapDomainLinearEquiv` are the linear forms of `mapDomain`, and the instance `MonoidAlgebra.instIsTorsionFree` passes torsion freeness from $S$ to $S[M]$.

#### Supports

The file `Mathlib.Algebra.MonoidAlgebra.Support` controls the support of a product. The lemma `MonoidAlgebra.support_coeff_mul_subset` says that the support of $xy$ lies in the pointwise product of the supports:
$$\operatorname{supp}(xy) \subseteq \operatorname{supp}(x) \cdot \operatorname{supp}(y).$$
Proof: by `MonoidAlgebra.mul_def`, $xy$ is a sum of single elements $(x(m_1) y(m_2)) \, (m_1 m_2)$ with $m_1$ and $m_2$ in the supports, and the support of a sum lies in the union of the supports. A count follows: `MonoidAlgebra.card_support_coeff_mul_le` bounds the size of the support of $xy$ by the product of the sizes. For a product with a single element, `MonoidAlgebra.support_coeff_mul_single_eq_image` gives equality: if $x$ is right regular in $M$ and $r$ is not a zero divisor on the right, the support of $f \cdot r \, x$ is the image of the support of $f$ under $m \mapsto m x$. Each element lies in the span of the elements $1 \, m$ of its support (`MonoidAlgebra.mem_span_support_coeff`). The support of $1$ is $\{1\}$ over a nontrivial ring (`MonoidAlgebra.support_coeff_one`).

#### Degrees and leading coefficients

The file `Mathlib.Algebra.MonoidAlgebra.Degree` works with a degree function $D \colon A \to B$ from an additive monoid $A$ to an ordered type $B$. The degree `AddMonoidAlgebra.supDegree` $D$ $p$ is the supremum of $D(a)$ over the support of $p$, and it is $\bot$ for $p = 0$. The lower degree `AddMonoidAlgebra.infDegree` is the infimum. For a polynomial in one variable, $D$ is the map $\mathbb{N} \to \text{WithBot } \mathbb{N}$, and `supDegree` is the degree. For several variables, $D$ can be the total degree of an exponent vector, a weighted degree, or the embedding of a monomial order.

For a linear order $B$ and an injective $D$, the maximum is reached at one point of the support, and `AddMonoidAlgebra.leadingCoeff` $D$ $p$ is the coefficient there. The predicate `AddMonoidAlgebra.Monic` $D$ $p$ says that this coefficient is $1$. The lemma `AddMonoidAlgebra.exists_supDegree_mem_support` says that a nonzero $p$ has a point of its support where the degree is reached.

The main estimates are the familiar ones. `AddMonoidAlgebra.supDegree_add_le` says $\operatorname{deg}(f + g) \le \operatorname{deg} f \sqcup \operatorname{deg} g$. Proof: the support of $f + g$ lies in the union of the supports, and the supremum over a union is the join of the suprema. For a $D$ with $D(a_1 + a_2) \le D(a_1) + D(a_2)$, `AddMonoidAlgebra.sup_support_coeff_mul_le` bounds the degree of a product by the sum of the degrees, by `MonoidAlgebra.support_coeff_mul_subset`. When $D$ is additive and injective and $B$ is strictly ordered, `AddMonoidAlgebra.coeff_supDegree_add_supDegree` says that the coefficient of $pq$ at the sum of the two top exponents is the product of the leading coefficients. Proof: a pair $(a_1, a_2)$ in the supports with $a_1 + a_2$ equal to the sum of the top exponents has $D(a_1) + D(a_2) = \deg p + \deg q$ with $D(a_1) \le \deg p$ and $D(a_2) \le \deg q$. Strict monotonicity forces both equalities, and injectivity of $D$ fixes $a_1$ and $a_2$. So only one term contributes. From this, `AddMonoidAlgebra.supDegree_mul` and `AddMonoidAlgebra.leadingCoeff_mul` give the exact degree and leading coefficient of a product when the product of the leading coefficients is not zero, and `AddMonoidAlgebra.Monic.mul` and `AddMonoidAlgebra.Monic.pow` say that monic elements are closed under products. The lemma `AddMonoidAlgebra.supDegree_sub_lt_of_leadingCoeff_eq` is the step of a division algorithm: two elements of the same degree and the same leading coefficient have a difference of smaller degree.

#### Division by a monomial

The file `Mathlib.Algebra.MonoidAlgebra.Division` divides by a single exponent $g$ in an additive cancellative commutative monoid $G$. The element `AddMonoidAlgebra.of'` $k$ $G$ $g$ is the monomial $1 \, g$. The quotient `AddMonoidAlgebra.divOf` $x$ $g$ has the coefficients $x(g + g')$ at $g'$ (`AddMonoidAlgebra.coeff_divOf`). The remainder `AddMonoidAlgebra.modOf` $x$ $g$ keeps the coefficients of $x$ at the points that are not of the form $g + d$ (`AddMonoidAlgebra.coeff_modOf_of_not_exists_add`) and is zero elsewhere. The identity `AddMonoidAlgebra.divOf_add_modOf` says $(1 \, g) \cdot (x \operatorname{div} g) + (x \operatorname{mod} g) = x$. Proof: compare the coefficients at $h$. If $h = g + d$ for some $d$, the first term gives $x(g + d) = x(h)$ by `AddMonoidAlgebra.coeff_divOf` and cancellation, and the second gives zero. Otherwise the first term gives zero and the second gives $x(h)$.

So $1 \, g$ divides $x$ exactly when the remainder is zero: this is `AddMonoidAlgebra.of'_dvd_iff_modOf_eq_zero`. The lemma `AddMonoidAlgebra.mul_of'_divOf` says that division undoes multiplication. The map `AddMonoidAlgebra.divOfHom` bundles the division as an action of `Multiplicative G` by additive endomorphisms. Section 6 applies these results to `MvPolynomial` with $G$ the exponent vectors.

#### Gradings

The file `Mathlib.Algebra.MonoidAlgebra.Grading` makes $R[M]$ a graded algebra. For a map $f \colon M \to \iota$, `AddMonoidAlgebra.gradeBy` $R$ $f$ $i$ is the submodule of elements whose support lies in $f^{-1}(i)$ (`AddMonoidAlgebra.mem_gradeBy_iff`). For $f$ the identity it is `AddMonoidAlgebra.grade` $R$ $m$, the multiples of $1 \, m$ (`AddMonoidAlgebra.mem_grade_iff`). The lemma `AddMonoidAlgebra.grade.isInternal` says that $R[M]$ is the internal direct sum of these submodules. Proof: each element is the sum of its terms $r_m \, m$, and the term $r_m \, m$ lies in the $m$th summand, so the sum map is surjective. The decomposition is unique because two decompositions have the same coefficients at each $m$. For an additive $f$, `AddMonoidAlgebra.gradeBy.isInternal` is the same result, and the instances `AddMonoidAlgebra.grade.gradedAlgebra` and `AddMonoidAlgebra.gradeBy.gradedAlgebra` give the structure of a graded algebra. The homogeneous components of `MvPolynomial` come from this file, with $f$ the total degree of an exponent vector.

#### No zero divisors

The file `Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors` gives a criterion for $R[A]$ to have no zero divisors. A magma $A$ has unique products when for any two nonempty finite sets $S, T \subseteq A$ some product $a_0 b_0$ with $a_0 \in S$, $b_0 \in T$ is written in only one way as a product of an element of $S$ and an element of $T$. The class is `UniqueProds`, and the additive version is `UniqueSums`. Linearly ordered cancellative monoids, such as $\mathbb{N}$, $\mathbb{N}^n$ and $\mathbb{Z}^n$, have unique products.

The key lemma is `MonoidAlgebra.coeff_mul_mul_of_uniqueMul`: if $a_0 b_0$ is a unique product of the supports of $f$ and $g$, then $(fg)(a_0 b_0) = f(a_0) \, g(b_0)$. Proof: by `MonoidAlgebra.coeff_mul_antidiag`, the coefficient is a sum over the pairs in the supports with product $a_0 b_0$, and there is only one such pair. So over a ring without zero divisors the product of two nonzero elements has a nonzero coefficient. This gives the instance `MonoidAlgebra.instNoZeroDivisorsOfUniqueProds`, the additive `AddMonoidAlgebra.instNoZeroDivisorsOfUniqueSums`, and over a domain with a monoid $A$ the instance `MonoidAlgebra.instIsDomainOfIsCancelAddOfUniqueProds`. This is how `Polynomial R` and `MvPolynomial σ R` are domains over a domain. The zero divisor conjecture asks whether $k[G]$ is a domain for every torsion free group $G$; groups with unique products are the main known case.

#### Ideals spanned by monomials

The file `Mathlib.Algebra.MonoidAlgebra.Ideal` has one result and its additive copy. The lemma `MonoidAlgebra.mem_ideal_span_of_image` says that $x$ lies in the ideal generated by the monomials $1 \, m'$ with $m' \in s$ exactly when each $m$ in the support of $x$ is a multiple $d m'$ of some $m' \in s$. Proof: the ideal is spanned as a module by the elements $(r \, d)(1 \, m') = r \, (d m')$, so each element of the ideal has its support among the multiples. Conversely, if each $m$ in the support is a multiple $d m'$, then $x = \sum r_m \, (1 \, d)(1 \, m')$ is in the ideal. The additive copy `AddMonoidAlgebra.mem_ideal_span_of'_image` is the source of `MvPolynomial.mem_ideal_span_monomial_image`, the description of monomial ideals in Section 2.

#### Direct sums

The file `Mathlib.Algebra.MonoidAlgebra.ToDirectSum` identifies `AddMonoidAlgebra M ι` with the direct sum $\bigoplus_{i \in \iota} M$, a dependent version of the same data. The maps `AddMonoidAlgebra.toDirectSum` and `DirectSum.toAddMonoidAlgebra` go in both directions, and `AddMonoidAlgebra.toDirectSum_single` sends $m \, i$ to the element $m$ in the summand $i$. The map respects products (`AddMonoidAlgebra.toDirectSum_mul`), because the product of a direct sum adds the indices. The bundled forms are `addMonoidAlgebraRingEquivDirectSum` and `addMonoidAlgebraAlgEquivDirectSum`. There is no multiplicative version, since the product of direct sums adds indices.

#### Common errors

1. Using `MonoidAlgebra.mapDomain` along a noninjective map and expecting it to keep the coefficients. Terms with the same image are added, so a coefficient can vanish. Use `MonoidAlgebra.comapDomain` only for an injective map.
2. Forgetting the hypotheses on $D$ in the degree lemmas. The exact formulas `AddMonoidAlgebra.supDegree_mul` and `AddMonoidAlgebra.leadingCoeff_mul` need $D$ additive and injective and a strictly ordered target. Without them only the inequalities hold.
3. Looking for a multiplicative `divOf`. The division file exists only for `AddMonoidAlgebra`, so for a multiplicative monoid move to the additive side with `MonoidAlgebra.toAdditive`.

### Exercises

1. (A) Use `MonoidAlgebra.mapDomain_single` to compute the image of $1 \, g + 1 \, g^{-1}$ in $\mathbb{Z}[G/H]$ for a normal subgroup $H$ and $g \in H$.
2. (A) Show with `AddMonoidAlgebra.mem_grade_iff` that the product of an element of degree $m$ and an element of degree $n$ lies in degree $m + n$.
3. (B) Prove with `MonoidAlgebra.support_coeff_mul_subset` that the elements supported in a submonoid $N$ of $M$ form a subring of $R[M]$.
4. (B) Use `MonoidAlgebra.mem_ideal_span_of_image` to show that $x^2 y$ is not in the ideal $(x^3, y^2)$ of $k[x, y]$.
5. (B) Show that $\mathbb{Z}$ has unique sums, and deduce from `MonoidAlgebra.coeff_mul_mul_of_uniqueMul` that the ring of Laurent polynomials $k[\mathbb{Z}]$ has no zero divisors.
6. (C) Show that for a finite group $G$ of order at least $2$, the element $\sum_{g \in G} 1 \, g$ is a zero divisor in $k[G]$, and explain why $G$ cannot have unique products.

### Reference

<?reference?>
