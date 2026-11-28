# The prime spectrum and local properties

The prime spectrum $\operatorname{Spec} R$ of a commutative ring is the set of its prime ideals with the Zariski topology. It turns a ring into a space, and it is the first step from commutative algebra to algebraic geometry. Many properties of rings and modules can be checked at each prime, or on an open cover of the spectrum, and this chapter collects these local principles.

Section 1 treats the prime spectrum and the Zariski topology: the zero loci and vanishing ideals, the basic open sets, closed points and irreducible closed sets, the Noetherian case, clopen sets and idempotents, and Jacobson rings. Section 2 treats the maps of spectra induced by ring maps, the spectrum of a quotient and of a polynomial ring, the free locus and the rank of a module at each prime, constructible sets and Chevalley's theorem, and the maximal spectrum. Section 3 treats local properties: the local principle for elements, submodules and exact sequences, the local nature of finite presentation, projectivity and homological dimensions, the framework of properties of ring maps, local isomorphisms and maps that are surjective on stalks.

The chapter uses the ideals and localizations of Volume 9 and the local rings of Chapter 2. Section 2 uses the integral extensions of Chapter 1 and the dimension theory of Chapter 7.

In Mathlib the main notions are `PrimeSpectrum R`, `PrimeSpectrum.zeroLocus`, `PrimeSpectrum.basicOpen`, `PrimeSpectrum.comap`, `MaximalSpectrum R` and `RingHom.PropertyIsLocal`.
