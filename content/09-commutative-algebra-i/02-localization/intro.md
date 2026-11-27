# Localization

Volume 6, Chapter 3 built the field of fractions of an integral domain. Its construction fails for a ring with zero divisors: the relation $a/s \sim b/t$ defined by $a t = b s$ is not transitive. This chapter inverts the elements of any multiplicative set $S$ of any commutative ring $R$. The result is a ring $S^{-1} R$ with a homomorphism $R \to S^{-1} R$ that is universal among the homomorphisms that send $S$ to units.

Section 1 builds $S^{-1} R$ with the corrected relation, proves its universal property, and states the characteristic predicate that Mathlib uses: a homomorphism $R \to A$ is a localization at $S$ if the elements of $S$ become units, every element of $A$ is a fraction, and the kernel consists of the elements killed by an element of $S$. It treats the main cases $R_f$ and $R_{\mathfrak{p}}$.

Section 2 compares the ideals of $R$ and of $S^{-1} R$. Every ideal of $S^{-1} R$ is an extended ideal, and the prime ideals of $S^{-1} R$ correspond to the prime ideals of $R$ that miss $S$. For a prime $\mathfrak{p}$ the ring $R_{\mathfrak{p}}$ is local: it has exactly one maximal ideal. Localization also commutes with quotients.

Section 3 puts a topology on the set of prime ideals, the Zariski topology on $\operatorname{Spec} R$. Its closed sets are the sets $V(I)$ and its basic open sets are the sets $D(f)$, which correspond to the localizations $R_f$. The section proves that $\operatorname{Spec} R$ is quasi-compact and describes its closed and irreducible subsets with the radicals of Chapter 1.

The chapter needs Chapter 1, Volume 6, Chapters 2 and 3, and the definition of a topological space from Volume 13. In Mathlib, localization is the predicate `IsLocalization`, local rings are `IsLocalRing`, and the spectrum is `PrimeSpectrum`. Volume 10 develops local rings and the spectrum further, and Chapter 3 of this volume uses localization to study Noetherian rings.
