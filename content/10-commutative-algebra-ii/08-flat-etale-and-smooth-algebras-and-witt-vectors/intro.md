# Flat, étale and smooth algebras, and Witt vectors

The last chapter collects properties of algebras that come from algebraic geometry. A flat module is one for which tensor product keeps injective maps injective; localizations, free and projective modules are flat, and over a Dedekind domain flat means torsion-free. The module of Kähler differentials $\Omega_{A/R}$ is the universal target of derivations, and it is the algebraic form of the cotangent bundle.

Section 1 treats flat modules and Kähler differentials, with the two exact sequences for $\Omega$. Section 2 uses them to define unramified, smooth and étale algebras through the infinitesimal lifting criteria, and proves that étale means unramified and smooth, that localizations and finite separable field extensions are étale, and that smooth algebras are flat. The section ends with the ring of Witt vectors $W(k)$ of a perfect field $k$ of characteristic $p$, a DVR of characteristic $0$ with residue field $k$, and its isomorphism $W(\mathbb{F}_p) \cong \mathbb{Z}_p$.

The chapter uses the local rings of Chapter 2, the DVRs of Chapter 3, the Dedekind domains of Chapter 4 and Hensel's lemma of Chapter 6. Tensor products are in Volume 8, and separable field extensions are in Volume 11.

In Mathlib the main classes are `Module.Flat R M`, `Algebra.Smooth R A`, `Algebra.Etale R A` and `Algebra.FormallyUnramified R A`, and the Witt vectors are `WittVector p R`, with notation `𝕎 R`.
