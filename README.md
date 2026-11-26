# The Mathlib Handbook

The Mathlib Handbook is a textbook of all the mathematics in Mathlib, the mathematical library of the Lean theorem prover. It is written by mathematicians for students. It comes as PDF, EPUB and HTML books, and it is true to the latest Mathlib.

Each section reads as a section of a textbook. It gives the definitions with their motivation, states the theorems, proves them on paper, works examples and sets exercises. Next to the mathematics, a Mathlib box says how the library states the same thing, with the real declaration names, and where Mathlib differs from the textbooks. Each Lean block comes from a checked file of [mathlib-lean](https://github.com/tamnd/mathlib-lean), so Lean checks every block against the Mathlib of the edition.

The site is https://mathlib.tamnd.com.

## Every declaration

Mathlib has about 330,000 declarations. The handbook explains each one at the depth that fits its role (spec 04 of tamnd/mathlib):

| Depth | Treatment |
|---|---|
| E3 | the main definitions and theorems: full textbook treatment, a proof on paper, examples that Lean checks, exercises |
| E2 | stated, with a short proof or a proof idea |
| E1 | one sentence in words, checked against the type |
| E0 | explained as a member of a family, such as the additive twins of multiplicative lemmas |

The Catalogue volumes list every declaration with its depth and its home section.

## Editions

The text follows Mathlib `master` each day. Each stable Mathlib tag `v4.X.0` gives an edition, and only editions are printed. An edition is named by its tag, so the v4.36.0 edition describes Mathlib `v4.36.0`. The copyright page of each book gives the Mathlib commit.

## The volumes

| Volume | Title | Level | Part |
|---|---|---|---|
| V00 | Guide: how to read Mathlib | guide | I. Foundations |
| V01 | The language of Mathlib | foundation | I. Foundations |
| V02 | Numbers | undergraduate | I. Foundations |
| V03 | Sets, finite structures and big operators | undergraduate | I. Foundations |
| V04 | Order and lattices | undergraduate | I. Foundations |
| V05 | Groups | undergraduate | II. Algebra |
| V06 | Rings, fields and ordered algebra | undergraduate | II. Algebra |
| V07 | Linear algebra | undergraduate | II. Algebra |
| V08 | Multilinear algebra and forms | graduate | II. Algebra |
| V09 | Commutative algebra I: ideals, polynomials, factorization | undergraduate to graduate | II. Algebra |
| V10 | Commutative algebra II: valuations, Dedekind domains, local algebra | graduate | II. Algebra |
| V11 | Fields and Galois theory | undergraduate to graduate | II. Algebra |
| V12 | Number theory | undergraduate to graduate | II. Algebra |
| V13 | General topology | undergraduate | III. Topology and analysis |
| V14 | Topological algebra and infinite sums | graduate | III. Topology and analysis |
| V15 | Real analysis in one variable | undergraduate | III. Topology and analysis |
| V16 | Normed spaces and functional analysis | graduate | III. Topology and analysis |
| V17 | Differential calculus in normed spaces | graduate | III. Topology and analysis |
| V18 | Measure and integration | graduate | III. Topology and analysis |
| V19 | Complex and harmonic analysis | graduate | III. Topology and analysis |
| V20 | Probability | graduate | III. Topology and analysis |
| V21 | Dynamics, ergodic theory and information theory | graduate | III. Topology and analysis |
| V22 | Affine, Euclidean and convex geometry | undergraduate | IV. Geometry |
| V23 | Manifolds and bundles | graduate | IV. Geometry |
| V24 | Category theory | graduate | V. Categories and their uses |
| V25 | Higher structures in categories | research | V. Categories and their uses |
| V26 | Homological algebra | graduate | V. Categories and their uses |
| V27 | Algebraic topology and condensed mathematics | graduate to research | V. Categories and their uses |
| V28 | Algebraic geometry | graduate | V. Categories and their uses |
| V29 | Representation theory and Lie theory | graduate | V. Categories and their uses |
| V30 | Combinatorics | undergraduate to graduate | VI. Discrete mathematics and logic |
| V31 | Set theory | graduate | VI. Discrete mathematics and logic |
| V32 | Logic, model theory and computability | graduate | VI. Discrete mathematics and logic |
| V33 | Data structures and computation | foundation | VI. Discrete mathematics and logic |
| V34 | The tactics of Mathlib | every Lean reader | VII. Tactics |

The status of each volume is on the site. A volume is released only when every chapter is reviewed and every Lean block builds (spec 12.6 of tamnd/mathlib).

## The repositories

| Repository | Content |
|---|---|
| [mathlib](https://github.com/tamnd/mathlib) | the map of Mathlib for the handbook: the volume map, the section plans, the records and the spec. It is not a fork of Mathlib |
| [mathlib-lean](https://github.com/tamnd/mathlib-lean) | the Lean package `MathlibHandbook`: the examples, the exercises, the solutions and the programs that read Mathlib |
| [mathlib-agent](https://github.com/tamnd/mathlib-agent) | `mlib`, the toolchain: the index, the sync, the coverage, the drift and the site |
| mathlib-handbook (this repository) | the text of the volumes and `mlhb`, the builder of the PDF, EPUB and HTML books |

## Licence

The text is CC BY 4.0 (`LICENSE-CONTENT`). The builder is MIT (`LICENSE`). The quoted Mathlib signatures and docstrings come from Mathlib under Apache-2.0. See `NOTICE`.
