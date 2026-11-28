# Graded algebras

A graded ring is a ring that splits as a direct sum of pieces $A_i$, indexed by a monoid, with $A_iA_j \subseteq A_{i+j}$. The polynomial ring graded by total degree is the main example. Its homogeneous ideals describe the subsets of projective space, and the degree zero parts of its localizations describe the affine charts. The algebra of this chapter is the input of the construction of projective schemes.

Section 1 defines graded rings and algebras, the decomposition into homogeneous components, the degree zero part and its finiteness properties, graded homomorphisms, base change, and filtered rings. Section 2 treats homogeneous ideals and submodules, the irrelevant ideal, the test for primality on homogeneous elements, and the radical. Section 3 constructs the homogeneous localization, proves that it is local at a prime, and shows for gradings by $\mathbb{N}$ that the charts glue and are of finite type.

The chapter uses ideals and localization from Volume 9, local rings from Chapter 2, and the internal gradings of the tensor and exterior algebras from Volume 8. The projective spectrum and its structure sheaf are in Volume 28.

In Mathlib the main classes are `GradedRing 𝒜` and `GradedAlgebra 𝒜`, the graded maps are `GradedRingHom`, the homogeneous ideals are `Ideal.IsHomogeneous` and `HomogeneousIdeal 𝒜`, and the homogeneous localization is `HomogeneousLocalization 𝒜 S`.
