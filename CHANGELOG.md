# Changelog

Each release has a section. The newest release is first.

## Unreleased

## v0.6.0 - 2026-11-27

### Changed

- `EDITION` pins mathlib at `1bb68c1a43`, mathlib-lean at `bf65eeb7fa` and mathlib-agent at `f71764a6aa`, the commits of their release v0.6.0.

### Added

- The first draft of V24 Category theory (8 chapters, 20 sections, 128 exercises, about 48,000 words). The volume gives the core of a first graduate course. Its intro names the topics that V25, V26 and V27 take. The status of each section is drafted, and each section has `lean: []`.
- The first draft of V21 Dynamics, ergodic theory and information theory (8 chapters, 21 sections, 125 exercises, about 43,000 words). The status of each section is drafted, and each section has `lean: []`.
- The first draft of V22 Affine, Euclidean and convex geometry (8 chapters, 22 sections, 136 exercises, about 44,000 words). With V22, every volume of the reading path U has a draft. The status of each section is drafted, and each section has `lean: []`.
- The first draft of V19 Complex and harmonic analysis (8 chapters, 22 sections, 127 exercises, about 44,000 words). The status of each section is drafted, and each section has `lean: []`.
- The first draft of V08 Multilinear algebra and forms (8 chapters, 20 sections, 133 exercises, about 44,000 words). The status of each section is drafted, and each section has `lean: []`.

## v0.5.1 - 2026-11-27

### Changed

- `EDITION` pins mathlib at `1660034bd0`, mathlib-lean at `d0fc806ca8` and mathlib-agent at `6ae6fe1737`, the commits of their release v0.5.1.

## v0.5.0 - 2026-11-27

### Changed

- `EDITION` pins mathlib at `1ade9058e3`, mathlib-lean at `66f312f6d9` and mathlib-agent at `dc6ac18b9a`, the commits of their release v0.5.0.

## v0.4.1 - 2026-11-27

### Changed

- `EDITION` pins mathlib at `122d829d79`, mathlib-lean at `63eec572ab` and mathlib-agent at `89acae1e6c`, the commits of their release v0.4.1.

### Added

- The first draft of V10 Commutative algebra II (8 chapters, 19 sections, 142 exercises, about 43,000 words). The status of each section is drafted, and each section has `lean: []`.
- The first draft of V20 Probability (8 chapters, 21 sections, 157 exercises, about 45,000 words). Chapters 1 to 5 hold the core of the reading path U. The status of each section is drafted, and each section has `lean: []`.
- The first draft of V16 Normed spaces and functional analysis (7 chapters, 19 sections, 140 exercises, about 44,000 words). The status of each section is drafted, and each section has `lean: []`.
- The first draft of V18 Measure and integration (8 chapters, 20 sections, 134 exercises, about 45,000 words). Chapters 1 to 6 hold the core of the reading path U. The status of each section is drafted, and each section has `lean: []`.
- The first draft of V12 Number theory (8 chapters, 19 sections, 141 exercises, about 45,000 words). The status of each section is drafted, and each section has `lean: []`.
- The first drafts of V11 Fields and Galois theory (8 chapters, 19 sections, 134 exercises) and V14 Topological algebra and infinite sums (8 chapters, 19 sections, 136 exercises), with about 89,000 words. The status of each section is drafted, and each section has `lean: []`.
- The first drafts of V09 Commutative algebra I: ideals, polynomials, factorization (7 chapters, 20 sections, 127 exercises) and V17 Differential calculus in normed spaces (8 chapters, 19 sections, 110 exercises), with about 89,000 words. The status of each section is drafted, and each section has `lean: []`.

## v0.4.0 - 2026-11-27

### Added

- The first drafts of V06 Rings, fields and ordered algebra (8 chapters, 22 sections), V07 Linear algebra (7 chapters, 17 sections), V13 General topology (8 chapters, 19 sections) and V15 Real analysis in one variable (7 chapters, 19 sections). The four volumes have about 208,000 words and 579 graded exercises. The status of each section is drafted. These volumes have no Lean blocks and no (L) exercises yet, and each section has `lean: []`.

### Changed

- `EDITION` pins mathlib at `ba62d45d36`, mathlib-lean at `ace216efc6` and mathlib-agent at `b038d7fcff`, the commits of their release v0.4.0.
- The line `catalogue` of `EDITION` gives all 35 volumes, V00 to V34. The CI sets the full Catalogue, C00 to C34, with each declaration of Mathlib in the volume of its home. A local build of C24, the largest new volume, gives 725 pages with 34,120 entries.

## v0.3.0 - 2026-11-27

### Added

- The first drafts of V02 Numbers, V03 Sets, finite structures and big operators, V04 Order and lattices, and V05 Groups. Each volume has eight chapters with one section each, and the companion files of tamnd/mathlib-lean#16 and #17. The status of each section is drafted.
- The line `catalogue` of `EDITION` gives the 21 volumes of Part I to Part III, V00 to V20. The CI sets C00 to C20, with about 218,000 entries.

### Changed

- `EDITION` pins mathlib at `be8e68c00b`, mathlib-lean at `391db40483` and mathlib-agent at `9bae1231d1`, the commits of their release v0.3.0.
- The text of V00, V01, V02, V03, V04, V05 and V34 is rewritten as a textbook for students. Each chapter has 2 to 4 sections, and each section has the definitions, the theorems with complete proofs, worked examples, the Mathlib boxes, the common errors of a learner and graded exercises with hints. The seven volumes have 114 sections and about 297,000 words, against 51,000 words before. The status of each section stays drafted.

## v0.2.0 - 2026-11-27

### Added

- `mlhb`, the builder of the books. It is a port of `mhb` of mmp-handbook, with the content model of spec 07 (volumes V00 to V34, chapters, sections with the kinds theory, api, instance, tactic, survey and guide), the Mathlib box, and the directives `<?decl?>`, `<?lean?>`, `<?reference?>` and `<?missing?>` of spec 12.4.
- `mlhb check` with the checks 1 to 9 of spec 12.3: the front matter and the parts, the Lean names and the deprecated names against the index, the anchors of mathlib-lean, the home volume of the modules, one home section for each E3 and E2 name, the `requires` ids and their cycles, the `reads_with` keys, the style and the exercise grades.
- `mlhb new volume` and `mlhb new section`, which write the front matter from the section plan of tamnd/mathlib.
- `tex/handbook.sty` with the copyright page of spec 12.7 and the Mathlib box, `tex/epub.css` and `filters/mlhb.lua`.
- A fixture library in `tests/fixture` and the tests of `mlhb`.
- The workflow `build`. It tests `mlhb`, builds the fixture with pandoc 3.12 and Tectonic 0.17.0 at pinned SHA-256 sums, and on a tag attaches the books of `content/` to the release with their sums and a build provenance attestation.
- Lean in print (spec 12.5). With `--highlight`, mlhb prints each `<?lean?>` block with the SubVerso tokens of the companion, and each constant of Mathlib links to its page. Each `<?decl?>` signature gets the same classes. The PDF uses the new `tex/lean.sty` and needs no shell escape.
- The text of V00 (Guide: how to read Mathlib), 5 chapters with 6 guide sections. It reads one theorem, a signature, a proof term and a tactic proof, shows how to find a declaration, and gives the junk values and one full proof read line by line.
- The first drafts of V01 (The language of Mathlib), 6 chapters with 1 theory section each, and of V34 (The tactics of Mathlib), 5 chapters with 2 tactic sections each. Each chapter has the status drafted and prints with the Draft mark.
- The book files of `books/`: MIL, TPIL, LLR and MSG.
- `mlhb catalogue` and `tex/catalogue.sty`, the Catalogue volumes of spec 06.4. The command sets the files of `mlib catalogue` of tamnd/mathlib-agent as a PDF in two columns and as an EPUB. The CI sets C01 to C05 and C13 for the editions. C05 has 24,928 entries on 446 pages.

### Changed

- `EDITION` pins mathlib at `42eaad8181`, mathlib-lean at `44682dff69` and mathlib-agent at `ff3ccab543`, the commits of their release v0.2.0.
- A volume that does not pass the release rule of spec 12.6 is a draft. Its files get `-draft` after the version, for example `mathlib-handbook-00-how-to-read-mathlib-0.2.0-draft.pdf`. Its copyright page says why it is a draft and gives its C-home and C-depth from `records/coverage.json` of tamnd/mathlib.
- The monospace font of the PDF is JuliaMono 0.63.2 (decision Q-08 of tamnd/mathlib). JuliaMono has a glyph for each of the 130 characters in the Lean blocks and the inline code of V00, V01 and V34. The fonts and the SIL Open Font License are in `tex/fonts`. DejaVu Sans Mono stays in the chain of fallback fonts.
- `EDITION` has two new lines. The line `mathlib-agent` pins mathlib-agent at `ed6297adfb`, and the line `catalogue` gives the Catalogue volumes of the books.
- The CI gets the index of Mathlib with `mlib index fetch`.
- `EDITION` pins mathlib-lean at `8c0d454ca3`, the commit with the Lean files of V00, V01 and V34, and Mathlib at `e54979a532`, the pin of that commit.

### Fixed

- A heading of level 3 now keeps 9 lines of space below it. Before, a table that started at the foot of a page put its header above the heading.

## v0.1.1 - 2026-11-26

### Changed

- `EDITION` pins mathlib at `a5c68e9183` and mathlib-lean at `31f707200e`, the commits of their release v0.1.1.

## v0.1.0 - 2026-11-26

### Changed

- `EDITION` pins mathlib at `29b279ceb0` and mathlib-lean at `c83443ca57`, the commits of their release v0.1.0.

## v0.0.2 - 2026-11-26

### Changed

- `EDITION` pins mathlib at `c2d9750d0c` and mathlib-lean at `11e7670ddb`, the commits of their release v0.0.2.

## v0.0.1 - 2026-11-26

### Added

- The README with the plan of the 35 volumes, the licences and the `NOTICE` for the quoted Mathlib material.
- The file `EDITION`, with the Mathlib commit of the edge.
- The workflows check and scorecard.
