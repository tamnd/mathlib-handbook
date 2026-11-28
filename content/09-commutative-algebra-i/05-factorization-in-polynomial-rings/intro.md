# Factorization in polynomial rings

Volume 6, Chapter 6 proves that a Euclidean domain is a principal ideal domain and that a principal ideal domain is a unique factorization domain. The polynomial ring $K[X]$ over a field $K$ is Euclidean, so its factorization theory is complete. The rings $\mathbb{Z}[X]$ and $K[X, Y]$ are not principal ideal domains, as $(2, X)$ and $(X, Y)$ show, but they still have unique factorization. This chapter proves that fact and gives the tests that decide whether a given polynomial is irreducible.

Section 1 defines the content and the primitive part of a polynomial over a unique factorization domain $R$. It proves Gauss's lemma: a product of primitive polynomials is primitive. From the lemma it follows that a primitive polynomial is irreducible over $R$ exactly when it is irreducible over the field of fractions $K$, and that $R[X]$ is a unique factorization domain. Induction then covers several variables.

Section 2 gives the criteria of irreducibility: the rational root test, the reduction modulo a prime and the criterion of Eisenstein. It applies them to $X^n - p$, to the cyclotomic polynomial $\Phi_p$ and to $X^4 + 1$. The last polynomial is irreducible over $\mathbb{Q}$, but it is reducible modulo every prime, so the converse of the reduction test is false.

Section 3 defines the formal derivative and uses it to detect multiple roots and square factors. It then builds the ring $R[X]/(f)$ in which $f$ has a root. This construction of Kronecker gives a field when $f$ is irreducible over a field.

Section 4 is a guide to the library of Euclidean domains and gcd monoids: the division and the extended gcd of `EuclideanDomain`, the classes `NormalizationMonoid` and `GCDMonoid`, gcds and lcms of finite sets and multisets, and the gcd monoids of $\mathbb{N}$ and $\mathbb{Z}$.

Section 5 is a guide to the library of unique factorization monoids and principal ideal domains: normalized factors, the characterizations by prime factors and by prime ideals, gcds in a unique factorization domain, and the theorem of Kaplansky.

Section 6 studies coprime elements in the sense of the Bezout identity, Bezout rings, the links to the gcd of a Euclidean domain and of $\mathbb{Z}$, chains of divisors, and finite domains: a finite domain is a field, and each finite subgroup of its units is cyclic. Section 7 describes the `AdjoinRoot` library: the maps and equivalences of $R[X]/(f)$, power bases for monic $f$, the presentation structure `IsAdjoinRoot`, the isomorphism $R[1/r] \cong R[X]/(rX - 1)$ and monic generators of ideals of $k[X]$.

Section 8 describes multiplicity, the Möbius function and the radical of an element of a unique factorization monoid. Section 9 collects the standard isomorphisms of polynomial rings: tensor products, matrices of polynomials, opposite rings and quotients, with polynomials over subrings and the integrality of coefficients. Section 10 treats the cyclotomic polynomials, their roots and their factorization over finite fields. Section 11 gives the classical families of Chebyshev, Dickson, Bernstein, Hermite, Pochhammer and shifted Legendre polynomials. Section 12 defines the resultant and the discriminant, states Vieta's formulas and builds the universal factorization ring.

The chapter needs the polynomial rings of Volume 6, Chapter 5, the irreducible and prime elements and the unique factorization domains of Volume 6, Chapter 6, and the quotient rings and prime ideals of Chapter 1. Volume 11 uses Section 3 for splitting fields.
