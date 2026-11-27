# Polynomials in several variables

A polynomial in several variables is a finite sum of terms $c \, x_1^{a_1} \cdots x_n^{a_n}$. The ring $k[x_1, \dots, x_n]$ of these polynomials is the ring of coordinates of the affine space $k^n$: each polynomial is a function on $k^n$, and the common zeros of a set of polynomials form an algebraic set. This chapter studies the ring and the link between its ideals and the algebraic sets.

Section 1 defines the ring for an arbitrary set of variables, as Mathlib does, and proves its universal property. It identifies $R[x_1, \dots, x_{n+1}]$ with $R[x_1, \dots, x_n][x_{n+1}]$, so that the results of Chapter 5 for one variable pass to several variables by induction. It then treats degrees and the values of polynomials over an infinite domain.

Section 2 starts the dictionary between algebra and geometry. It defines the zero set $V(I)$ of an ideal and the ideal $I(X)$ of a set of points. It then defines monomial orders, proves that the division algorithm in several variables terminates, proves Dickson's lemma on monomial ideals, and obtains Hilbert's basis theorem for $k[x_1, \dots, x_n]$ again by leading terms.

Section 3 proves Hilbert's Nullstellensatz over an algebraically closed field $k$. The weak form says that a proper ideal has a common zero. The maximal ideals of $k[x_1, \dots, x_n]$ are then the ideals of points. The strong form says that $I(V(I))$ is the radical of $I$. Together they give a bijection between radical ideals and algebraic sets.

The chapter needs the polynomial rings of Volume 6, Chapter 5, the radicals of Chapter 1, Section 2, the Noetherian rings and the Hilbert basis theorem of Chapter 3, Section 2, and the unique factorization of Chapter 5, Section 1. Volume 10 continues with the prime spectrum, the dimension of a variety and the local rings at its points.
