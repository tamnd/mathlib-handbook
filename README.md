# The Mathlib Handbook

The Mathlib Handbook is a textbook of all the mathematics in Mathlib, the mathematical library of the Lean theorem prover. It is written by mathematicians for students. It comes as PDF, EPUB and HTML books, and it is true to the latest Mathlib.

## Download

The PDF and EPUB files of each volume and of the Catalogue are on the [latest release](https://github.com/tamnd/mathlib-handbook/releases/latest). A volume that no person has reviewed yet has `-draft` in its file name, and its copyright page says why.

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

The folder `content/` has the text of V00 (5 chapters), V01 (6 chapters), V02 to V06 (8 chapters each), V07 (7 chapters), V09 (7 chapters), V13 (8 chapters), V15 (7 chapters), V17 (8 chapters) and V34 (5 chapters): 230 sections and about 594,000 words. Each section has complete proofs, worked examples, Mathlib boxes and graded exercises. No person has reviewed the sections yet, so each volume is a draft. The folder `books/` has the books that the sections read with: MIL, TPIL, LLR and MSG. The status of each volume is on the site. A volume is released only when every chapter is reviewed and every Lean block builds (spec 12.6 of tamnd/mathlib).

## The repositories

| Repository | Content |
|---|---|
| [mathlib](https://github.com/tamnd/mathlib) | the map of Mathlib for the handbook: the volume map, the section plans, the records and the spec. It is not a fork of Mathlib |
| [mathlib-lean](https://github.com/tamnd/mathlib-lean) | the Lean package `MathlibHandbook`: the examples, the exercises, the solutions and the programs that read Mathlib |
| [mathlib-agent](https://github.com/tamnd/mathlib-agent) | `mlib`, the toolchain: the index, the sync, the coverage, the drift and the site |
| mathlib-handbook (this repository) | the text of the volumes and `mlhb`, the builder of the PDF, EPUB and HTML books |

## Build the books

`mlhb` is the builder. It is a copy of `mhb` of [mmp-handbook](https://github.com/tamnd/mmp-handbook) with the parts that a book about a library needs. It needs Python 3.11 or later, pandoc 3.12 and Tectonic 0.17.0. The CI installs the two programs from their release files and checks the SHA-256 sums.

```sh
pip install ".[test]"
python -m mlhb check                      # the checks of spec 12.3
python -m mlhb resolve                    # resolve the directives and print the faults
python -m mlhb number --write             # write the statement numbers into the sources
python -m mlhb build --volume V13 --formats html,pdf,epub
python -m mlhb new volume V13
python -m mlhb new section V13/C05 compactness-in-metric-spaces
```

Each command takes `--map` (a checkout of tamnd/mathlib, default `../mathlib`), `--lean` (a checkout of tamnd/mathlib-lean, default `../mathlib-lean`), `--index` (the file `index.jsonl.gz` of the release `index` of tamnd/mathlib), `--highlight` (the unpacked tarball of the release `highlighted` of tamnd/mathlib-lean) and `--content` (default `content/`). Without an index, the checks of the Lean names do not run, and a build with a `<?decl?>` stops. Without the highlighted files, each `<?lean?>` block prints as plain Lean text.

A section file has the front matter of spec 07.7 and the parts of spec 07.3 as `###` headings. The builder replaces these directives:

| Directive | Replaced by |
|---|---|
| `<?decl Name?>` | the signature of `Name` from the index, as a Lean block |
| `<?lean path#anchor?>` | the Lean text between `-- anchor: anchor` and `-- end: anchor` of a file of mathlib-lean |
| `<?reference?>` | the reference table of the section: the E3, E2 and E1 declarations and the families |
| `<?missing?>` | the list `missing` of `volume.yaml` |

A directive that does not resolve stops the build. A Mathlib box is the fenced div `::: mathlib`. Its first line is `` `Name` · `Module` ``, and the builder makes links to the declaration page of the site and to the Mathlib documentation.

The Catalogue volumes C01 to C34 (spec 06.4) come from `mlib catalogue` of [mathlib-agent](https://github.com/tamnd/mathlib-agent). The command writes one file `C<NN>.jsonl.gz` for each main volume, and `mlhb catalogue` sets each file as a PDF in two columns and as an EPUB:

```sh
mlib index fetch -commit e54979a532 -out idx
mlib catalogue -index idx -map ../mathlib -volume V01,V13 -out catalogue
python -m mlhb catalogue --data catalogue --formats pdf,epub --out build
```

The line `catalogue` of `EDITION` gives the volumes that the CI sets, and the line `mathlib-agent` gives the commit of mlib. Each entry gives the Lean name, the kind, the attributes, the depth, the home section and one sentence. The sentence comes from a checked E1 record, then from the E0 family, then from the docstring of Mathlib. The preface of each Catalogue gives the count of each source.

The output files are named `mathlib-handbook-<NN-slug>-<version>+mathlib-<tag>.pdf` and `.epub`. A volume with a chapter that is not reviewed is a draft. Its files get `-draft` after the version, and its copyright page says why. The fixture library of `tests/fixture` has one volume with one section. The CI builds it on each pull request.

## Licence

The text is CC BY 4.0 (`LICENSE-CONTENT`). The builder is MIT (`LICENSE`). The quoted Mathlib signatures and docstrings come from Mathlib under Apache-2.0. See `NOTICE`.
