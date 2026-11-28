# Enumeration and partitions

Enumerative combinatorics counts finite structures exactly. A typical answer is a formula, a recursion or a generating function for the number of structures of size $n$. This chapter counts lattice paths and trees, partitions of integers, partitions of sets, and permutations with conditions on their cycles. Each count starts from a decomposition of a structure into smaller structures, and the decomposition gives a recursion.

Section 1 proves that the Catalan numbers $C_n = \binom{2n}{n}/(n + 1)$ count the Dyck words and the binary trees with $n$ nodes. It proves the closed form twice, by the telescoping sum of Mathlib and by the reflection argument, and it defines the Schröder numbers.

Section 2 studies partitions of integers. It proves the product formula for their generating functions, the theorem of Glaisher with the theorem of Euler on odd and distinct parts as a special case, by generating functions and by a bijection. It draws partitions as Young diagrams, defines the conjugate partition by the transpose, and proves the pentagonal number theorem of Euler by the involution of Franklin. It ends with semistandard Young tableaux.

Section 3 counts partitions of sets and permutations. It proves the recursions of the Stirling numbers of both kinds, of the Bell numbers and of the derangement numbers from the structures that they count. It proves the principle of inclusion and exclusion, the closed formula for the derangements and the limit $D(n)/n! \to 1/e$, and the principle of double counting.

Section 4 counts the compositions of an integer as ordered lists of blocks and defines the incidence algebra of a locally finite order, with its zeta and Möbius functions and the principle of Möbius inversion.

All sections need Volume 3, Chapters 3 and 6. Section 2 also needs formal power series from Volume 9, Chapter 7 and infinite products from Volume 14, Chapter 7. Section 3 also needs the cycles of permutations from Volume 5, Chapter 7 and the exponential series from Volume 15, Chapter 5. The level is a first undergraduate course in combinatorics, and the standard references are Stanley, *Enumerative Combinatorics*, and Andrews, *The Theory of Partitions*.

In Mathlib, the enumerative files often define a number by its recursion and prove the identities of the recursion, without a proof that the number counts the structures of its name. This is the case for the Stirling numbers and the Bell numbers. The sections of this chapter give the counting proofs on paper and say in each box what the library proves.
