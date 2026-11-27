# Quadratic residues and reciprocity

An integer $a$ is a quadratic residue modulo a prime $p$ when the congruence $x^2 \equiv a \pmod p$ has a solution. This chapter asks which $a$ are residues for a given $p$, and which $p$ have a given residue $a$. Section 1 counts the squares of `ZMod p`, proves Euler's criterion $a^{(p-1)/2} \equiv \pm 1$, defines the Legendre symbol $\left(\frac{a}{p}\right)$, and proves that it is multiplicative in $a$. Section 2 proves the lemmas of Gauss and Eisenstein and then the law of quadratic reciprocity with Eisenstein's count of lattice points, together with the supplementary laws for $-1$ and $2$. Section 3 extends the symbol to an odd modulus $n$ that is not prime, the Jacobi symbol, proves its reciprocity law, and gives the algorithm that computes $\left(\frac{a}{n}\right)$ without the factorization of $n$.

The chapter needs the field `ZMod p` and Euler's theorem from Volume 2, Chapter 6, the cyclic groups of Volume 5, Chapter 3, and the rings $\mathbb{Z}/n$ of Volume 6, Chapter 4.

Chapter 4 uses the Legendre symbol to decide which numbers are sums of two squares. Chapter 6 views the Legendre symbol as the first nontrivial Dirichlet character.
