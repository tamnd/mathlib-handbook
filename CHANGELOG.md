# Changelog

Each release has a section. The newest release is first.

## Unreleased

### Added

- The first drafts of V02 Numbers, V03 Sets, finite structures and big operators, V04 Order and lattices, and V05 Groups. Each volume has eight chapters with one section each, and the companion files of tamnd/mathlib-lean#16 and #17. The status of each section is drafted.

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
