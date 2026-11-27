# Clifford algebras

A quadratic form $Q$ on a module $M$ gives an algebra in which every vector squares to its value under $Q$. This is the Clifford algebra $\mathrm{Cl}(Q)$. For the zero form it is the exterior algebra of Chapter 4. For the form $-x^2$ on $\mathbb{R}$ it is the field of complex numbers, and for a form in two variables it is a quaternion algebra. In general, orthogonal vectors anticommute, and the algebra has rank $2^n$ when $M$ has an orthogonal basis of $n$ vectors.

Section 1 defines $\mathrm{Cl}(Q)$ as a quotient of the tensor algebra of Chapter 3 and proves its universal property. It proves the rule $\iota(x)\iota(y) + \iota(y)\iota(x) = B(x, y)$ for the polar form $B$, and the theorem on the rank. It computes the Clifford algebras that give the complex numbers, the quaternions and the dual numbers, and it shows that the form $x^2$ gives a ring with zero divisors.

Section 2 proves that $\mathrm{Cl}(Q)$ is graded by $\mathbb{Z}/2$, defines the grade involution and the reversion, and shows that the even part is itself a Clifford algebra of a module of rank one less. It then defines the Lipschitz, pin and spin groups. Conjugation by a vector acts on $M$ as a reflection, up to sign, and the spin group of the plane is a circle that covers the rotations twice.

The chapter needs the quadratic forms and the polar form of Chapter 6, the orthogonal bases of Chapter 5, the tensor algebra and the graded algebras of Chapter 3, and the exterior algebra of Chapter 4. Mathlib defines the polar form without a factor $\frac{1}{2}$, so most results hold over any commutative ring. A few, such as the linear isomorphism with the exterior algebra, need $2$ to be a unit. The spin groups of Section 2 act on $M$ through the isometries of Chapter 5.
