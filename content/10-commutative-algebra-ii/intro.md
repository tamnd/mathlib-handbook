# Commutative algebra II: valuations, Dedekind domains, local algebra

This volume continues the commutative algebra of Volume 9. Volume 9 has ideals, Noetherian rings, polynomial rings, factorization and the basics of localization. This volume treats the parts of commutative algebra that are used in algebraic number theory and algebraic geometry: integral extensions, local rings, valuations, Dedekind domains and their class groups, completions, dimension, and the properties of algebras that come from geometry.

The chapters are in order of dependence.

- Chapter 1, integral extensions: integral elements, the integral closure, normal domains, and lying over and going up.
- Chapter 2, local rings and Nakayama's lemma: local rings, localization at a prime, the residue field, and Nakayama's lemma with its applications to finitely generated modules.
- Chapter 3, valuations and discrete valuation rings: valuations and valuation rings, and the many equivalent definitions of a DVR.
- Chapter 4, Dedekind domains: the definition, fractional ideals and their invertibility, unique factorization of ideals, and the local characterization by DVRs.
- Chapter 5, the class group: the group of fractional ideals modulo principal ones, the criterion for a PID, and the computation of the class group of $\mathbb{Z}[\sqrt{-5}]$.
- Chapter 6, completions and adic topologies: filtrations, the Artin-Rees lemma, the Krull intersection theorem, the adic completion and Henselian rings.
- Chapter 7, Krull dimension: the dimension of a ring, its behavior under quotients and polynomial rings, and the regular local rings.
- Chapter 8, flat, étale and smooth algebras and Witt vectors: flat modules, Kähler differentials, the infinitesimal lifting criteria, and the Witt vectors of a perfect field.

Each section states the definitions and theorems with proofs in the usual mathematical form, and then shows the Mathlib names for them. The names are given in boxes, each with the module in which it is declared. Where a result is not in Mathlib, the text says that the index of this edition has no declaration for it.

The reader needs the ring theory of Volume 5 and the modules of Volume 7, and is assumed to know the material of Volume 9. Chapter 8 uses the tensor products of Volume 8. Number fields, the $p$-adic numbers and the class number are the subject of Volume 12, which applies the Dedekind domains and class groups of this volume. The topological side of adic completions is in Volume 14.

The examples are chosen so that they can be computed by hand: the rings $\mathbb{Z}[i]$, $\mathbb{Z}[\sqrt{-5}]$, $k[X, Y]/(Y^2 - X^3)$, the localizations $\mathbb{Z}_{(p)}$, and the power series rings $k[[X]]$. The exercises are graded (A) for direct checks, (B) for standard results, and (C) for harder problems.

All names refer to Mathlib at the commit given in the front matter of each section.
