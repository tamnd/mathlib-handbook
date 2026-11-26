# Changelog

Each release has a section. The newest release is first.

## Unreleased

### Added

- `mlhb`, the builder of the books. It is a port of `mhb` of mmp-handbook, with the content model of spec 07 (volumes V00 to V34, chapters, sections with the kinds theory, api, instance, tactic, survey and guide), the Mathlib box, and the directives `<?decl?>`, `<?lean?>`, `<?reference?>` and `<?missing?>` of spec 12.4.
- `mlhb check` with the checks 1 to 9 of spec 12.3: the front matter and the parts, the Lean names and the deprecated names against the index, the anchors of mathlib-lean, the home volume of the modules, one home section for each E3 and E2 name, the `requires` ids and their cycles, the `reads_with` keys, the style and the exercise grades.
- `mlhb new volume` and `mlhb new section`, which write the front matter from the section plan of tamnd/mathlib.
- `tex/handbook.sty` with the copyright page of spec 12.7 and the Mathlib box, `tex/epub.css` and `filters/mlhb.lua`.
- A fixture library in `tests/fixture` and the tests of `mlhb`.
- The workflow `build`. It tests `mlhb`, builds the fixture with pandoc 3.12 and Tectonic 0.17.0 at pinned SHA-256 sums, and on a tag attaches the books of `content/` to the release with their sums and a build provenance attestation.
- Lean in print (spec 12.5). With `--highlight`, mlhb prints each `<?lean?>` block with the SubVerso tokens of the companion, and each constant of Mathlib links to its page. Each `<?decl?>` signature gets the same classes. The PDF uses the new `tex/lean.sty` and needs no shell escape.

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
