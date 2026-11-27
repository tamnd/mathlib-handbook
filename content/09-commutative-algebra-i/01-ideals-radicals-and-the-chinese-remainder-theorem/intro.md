# Ideals, radicals and the Chinese remainder theorem

Volume 6, Chapter 2 defined ideals, their sums, products and intersections, the quotient ring $R/I$, and prime and maximal ideals. This chapter treats the ideals of a commutative ring as elements of a lattice with a product, and it develops the operations that the rest of the volume uses.

Section 1 studies the lattice of ideals, products, the modular law and the ideal quotient $(I : J)$. It then studies extension and contraction of ideals along a ring homomorphism $f : R \to S$. The two operations form a Galois connection. The section ends with coprime ideals and the rule that $I + J = R$ implies $I^m + J^n = R$.

Section 2 defines the radical $\sqrt{I}$ of an ideal, the nilradical and the Jacobson radical. Its main theorem says that $\sqrt{I}$ is the intersection of the prime ideals that contain $I$. The proof uses Zorn's lemma to find a prime ideal that avoids a multiplicative set. The section also proves that minimal prime ideals exist and that $x$ is in the Jacobson radical if and only if $1 - x y$ is a unit for each $y$.

Section 3 proves the Chinese remainder theorem for finitely many pairwise coprime ideals, relates it to idempotents and to products of rings, and computes $\mathbb{Z}/360$ and Lagrange interpolation as instances. It ends with the prime avoidance lemma.

The chapter needs Volume 6, Chapters 2 and 3, and Zorn's lemma from Volume 4. In Mathlib the ideals of a commutative ring form the complete lattice `Ideal R`, and most results are in the folder `Mathlib/RingTheory/Ideal`. Chapter 2 builds on Sections 1 and 2, Chapter 3 uses the operations of Section 1 for primary decomposition, and Chapter 4 uses the Jacobson radical in Nakayama's lemma and the Chinese remainder theorem in the structure of Artinian rings.
