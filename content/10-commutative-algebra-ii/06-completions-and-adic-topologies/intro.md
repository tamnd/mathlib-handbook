# Completions and adic topologies

An ideal $I$ of a ring defines a notion of nearness: two elements are close when their difference lies in a high power of $I$. The resulting $I$-adic topology and its completion give the $p$-adic integers from $\mathbb{Z}$ and the power series rings from polynomial rings. Completion keeps much of the algebra of a Noetherian ring and makes it easier to solve equations, by successive approximation.

Section 1 defines filtrations and stable filtrations, and proves the Artin-Rees lemma and the Krull intersection theorem for Noetherian rings. The intersection theorem says that the $I$-adic topology of a finite module is Hausdorff when $I$ is in the Jacobson radical, so a Noetherian local ring embeds in its completion. Section 2 defines the adic completion, proves that it is complete for a finitely generated ideal, proves Hensel's lemma for complete rings, and shows that over a Noetherian ring completion is exact on finite modules and flat.

The chapter uses Nakayama's lemma and the Jacobson radical from Chapter 2, and the Hilbert basis theorem from Volume 9. The general theory of topological rings and uniform completions is in Volume 14, and the $p$-adic numbers as a field are in Volume 12.

In Mathlib the filtrations are `Ideal.Filtration`, the completion is `AdicCompletion I M`, completeness is the class `IsAdicComplete I M`, and the Henselian property is `HenselianLocalRing`.
