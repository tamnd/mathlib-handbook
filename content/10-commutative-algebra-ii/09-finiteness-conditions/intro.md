# Finiteness conditions

Most theorems of commutative algebra need a finiteness hypothesis. A module can be finitely generated, a submodule can have a finitely generated quotient, a module can have finite length, and an algebra can be of finite type, finitely presented or essentially of finite type. This chapter collects these conditions and the results that move them along maps, towers and base change.

Section 1 treats finite modules and finitely generated submodules: the closure properties, extensions, finitely generated ideals and their radicals, cofinitely generated submodules, modules of finite length, descent along faithfully flat maps and bases in towers of algebras. Section 2 treats algebras of finite type and finitely presented algebras, the comparison over a Noetherian ring, base change, the algebras that are essentially of finite type, and the local criteria on an open cover of the spectrum.

The chapter uses the linear algebra of Volume 7, the tensor products of Volume 8, and the ideals, localizations and Noetherian rings of Volume 9.

In Mathlib the main notions are `Submodule.FG`, `Module.Finite R M`, `IsFiniteLength R M`, `Algebra.FiniteType R A`, `Algebra.FinitePresentation R A` and `Algebra.EssFiniteType R A`. The ring map forms are `RingHom.Finite`, `RingHom.FiniteType` and `RingHom.FinitePresentation`.
