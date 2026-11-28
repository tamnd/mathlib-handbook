# Matrix algebras and other constructions

This chapter collects constructions of algebras and modules that use tensor products and that do not fit in the earlier chapters. Matrix algebras are the basic algebras that are not commutative, and their modules are the same as the modules over the base ring. The other constructions are linear disjointness of subalgebras, the quadratic algebras, polynomial laws between modules and the Grassmannian functor.

Section 1 treats matrix algebras as tensor products and the Kronecker product, Morita equivalence and the Morita equivalence between a ring and its matrix rings, the Orzech property with its consequence that surjective endomorphisms of finitely generated modules are bijective, and ring involutions. Section 2 treats linearly disjoint subalgebras, the trace, norm and discriminant of a quadratic algebra, polynomial laws and the Grassmannian of a module.

The chapter uses the tensor products of Volume 8, the Azumaya algebras of Chapter 11, the flat modules of Chapter 8 and the rank of a module at a prime from Chapter 12.

In Mathlib the main notions are `matrixEquivTensor`, `IsMoritaEquivalent R A B`, `OrzechProperty R`, `Subalgebra.LinearDisjoint`, `QuadraticAlgebra R a b`, `PolynomialLaw R M N` and `Module.Grassmannian R M k`.
