"""The tests of mlhb on the fixture library of tests/fixture."""

import os
import shutil

import pytest

from mlhb.book import Book, out_name
from mlhb.check import check
from mlhb.resolve import ResolveError, resolve

HERE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fixture")


def book(content=None, highlight=""):
    return Book(content or os.path.join(HERE, "content"), os.path.join(HERE, "map"),
                os.path.join(HERE, "index.jsonl.gz"), os.path.join(HERE, "lean"), highlight=highlight)


def test_load():
    b = book()
    v = b.volume("V13")
    assert b.volume(13) is v
    assert v.id == "V13" and v.item_prefix == "13."
    ch = v.chapters[0]
    assert ch.id == "C05" and ch.status == "drafted"
    s = ch.sections[0]
    assert s.id == "V13.C05.S01" and s.e1_auto
    assert s.explains == {"E3": ["Metric.isCompact_iff_isClosed_bounded"]}
    assert b.map.index_commit.startswith("4472534b")
    assert b.map.decls["Metric.bounded_closedBall"].deprecated == "Metric.isBounded_closedBall"


def test_markdown():
    b = book()
    md, st = b.markdown(b.volume("V13"))
    assert "Theorem 13.5.2 (Heine and Borel)." in md
    assert "Definition 13.5.1 (Bounded set)." in md
    assert r"\LeanKw{theorem} \LeanConst{Metric.isCompact_iff_isClosed_bounded} : \LeanKw{∀} \LeanOB{}α" in md
    assert '<span class="lean-keyword">theorem</span> <a class="lean-const" href=' in md
    assert "isCompact_closedBall 0 1" in md
    assert "-- anchor" not in md
    assert "| [`Metric.isBounded_closedBall`](https://mathlib.tamnd.com/decl/Metric.isBounded_closedBall/) | theorem | A closed ball is bounded. | E1 | simp |" in md
    assert "Metric.bounded_closedBall" not in md   # a deprecated alias has no row
    assert "| F-simp | family |" in md
    assert "https://mathlib.tamnd.com/decl/Metric.isCompact_iff_isClosed_bounded/" in md
    assert "Mathlib/Topology/MetricSpace/Bounded.html#Metric.isCompact_iff_isClosed_bounded" in md
    assert "The lemma [`Metric.isBounded_closedBall`](https://mathlib.tamnd.com/decl/Metric.isBounded_closedBall/)" in md
    assert "**Rud76**. Walter Rudin. *Principles of Mathematical Analysis*. 1976." in md
    assert "**Draft.**" in md
    assert st["boxes"] == 1


def test_resolve_fails():
    b = book()
    v = b.volume("V13")
    s = v.chapters[0].sections[0]
    with pytest.raises(ResolveError, match="Nope is not in the index"):
        resolve(b.map, v, s, "<?decl Nope?>")
    with pytest.raises(ResolveError, match="no anchor gone"):
        resolve(b.map, v, s, "<?lean MathlibHandbook/V13/C05/Examples.lean#gone?>")
    with pytest.raises(ResolveError, match="no list missing"):
        resolve(b.map, v, s, "<?missing?>")
    assert resolve(b.map, v, s, "```\n<?decl Nope?>\n```") == "```\n<?decl Nope?>\n```"


def test_check_clean():
    b = book()
    faults, warns = check(b.volumes, b.map, HERE)
    assert faults == []
    assert warns == []


def test_check_faults(tmp_path):
    content = tmp_path / "content"
    shutil.copytree(os.path.join(HERE, "content"), content)
    shutil.copytree(os.path.join(HERE, "books"), tmp_path / "books")
    p = content / "13-general-topology" / "05-compactness" / "01-compactness-in-metric-spaces.md"
    t = p.read_text(encoding="utf-8")
    t = t.replace("requires: [V13.C02]", "requires: [V13.C09, V13.C05]")
    t = t.replace("reads_with: [\"Rud76 §2.C\"]", "reads_with: [\"Mun00 §28\"]")
    t = t.replace("  - Mathlib.Topology.MetricSpace.Bounded\n", "  - Mathlib.Topology.MetricSpace.Bounded\n  - Mathlib.Algebra.Group.Defs\n")
    t = t.replace("E3: [Metric.isCompact_iff_isClosed_bounded]", "E3: [Metric.isCompact_iff_isClosed_bounded, Metric.bounded_closedBall, Gone]")
    t = t.replace("#closedUnitBall", "#gone")
    t = t.replace("This section states", "We state")
    t = t.replace("3. (B) Show", "3. Show")
    t = t.replace("### Notes and history\n\nThe result is due to Heine and Borel.\n\n", "")
    p.write_text(t, encoding="utf-8")
    b = book(str(content))
    faults, _ = check(b.volumes, b.map, str(tmp_path))
    text = "\n".join(faults)
    assert "the requires id 'V13.C09' does not exist" in text
    assert "requires: a cycle V13.C05 -> V13.C05" in text
    assert "the reads_with key 'Mun00' is not in books/" in text
    assert "the module Mathlib.Algebra.Group.Defs has its home in V04" in text
    assert "Metric.bounded_closedBall is deprecated; use Metric.isBounded_closedBall" in text
    assert "Gone is not in the index" in text
    assert "the file has no anchor gone" in text
    assert "style: the word 'we'" in text
    assert "an exercise with no grade" in text
    assert "no part '### Notes and history'" in text


def test_out_name():
    v = book().volume("V13")
    # the chapter of the fixture is not reviewed, so the volume is a draft
    assert v.draft and v.reviewed == 0
    assert out_name(v, "0.2.0", "v4.38.0") == "mathlib-handbook-13-general-topology-0.2.0-draft+mathlib-v4.38.0"
    for c in v.chapters:
        for s in c.sections:
            s.fm["status"] = "reviewed"
    assert not v.draft and book().draft_note(v) == ""
    assert out_name(v, "0.2.0") == "mathlib-handbook-13-general-topology-0.2.0"


def test_draft_note():
    b = book()
    note = b.draft_note(b.volume("V13"))
    assert note.startswith("This volume is a draft.") and "because no chapter is reviewed by a person yet." in note


def test_highlight():
    b = book(highlight=os.path.join(HERE, "highlight"))
    md, _ = b.markdown(b.volume("V13"))
    assert r"\LeanKw{example} : \LeanConst{IsCompact} (\LeanConst{Metric.closedBall} (\LeanNum{0}" in md
    # ProperSpace.isCompact_closedBall is not a name of the fixture index, so it has no link
    assert '<span class="lean-const" title="ProperSpace.isCompact_closedBall.{u} {α : Type u}' in md
    assert "(Metric.closedBall x r)\">isCompact_closedBall</span>" in md
    assert "-- anchor" not in md and "public import" not in md
    faults, _ = check(b.volumes, b.map, os.path.dirname(b.content), b.volumes)
    assert faults == []


def test_highlight_anchor_missing(tmp_path):
    from mlhb.lean import Store
    with pytest.raises(KeyError):
        Store(os.path.join(HERE, "highlight")).anchor("MathlibHandbook/V13/C05/Examples.lean#nothing")
    with pytest.raises(KeyError):
        Store(str(tmp_path)).anchor("MathlibHandbook/V13/C05/Examples.lean#closedUnitBall")


def test_catalogue():
    from mlhb import catalogue
    h, rows = catalogue.load(os.path.join(HERE, "catalogue", "C13.jsonl.gz"))
    assert h["catalogue"] == "C13" and len(rows) == 4
    assert catalogue.title(h) == "Catalogue of General topology"
    assert catalogue.title({"title": "The tactics of Mathlib"}) == "Catalogue of the tactics of Mathlib"
    assert catalogue.out_name(h, "0.2.0") == "mathlib-handbook-c13-catalogue-of-general-topology-0.2.0"
    assert catalogue.families(rows) == [("F-instance", "An instance tells Lean that a type has a structure.", 1)]
    # the kind instance is not repeated as an attribute
    assert catalogue.meta(rows[1]) == "instance · E0 · V13.C05.S01"
    assert catalogue.text_tex(rows[2]["text"]) == r"The closed ball of radius r is in \texttt{Metric.ball x s} when r < s."
    body = catalogue.latex_body(h, rows)
    assert r"\hbcatmodule{\texttt{Mathlib.Topology.MetricSpace.Pseudo.Defs}}" in body
    assert r"instance · E0 · V13.C05.S01 · F-instance}{}" in body
    assert r"\hbcatdoc" in body and r"1 (25.0\%)" in body
    md = catalogue.epub_md(h, rows, "0.2.0", "2026-11-27")
    assert "- **F-instance** (1 entries)." in md
    assert "- **`Metric.closedBall_subset`** *theorem · simp · E1 · V13.C05.S01*." in md


def test_log_missing(tmp_path):
    from mlhb.latex import log_missing
    (tmp_path / "main.log").write_text(
        "Missing character: There is no ⨍ (U+2A0D) in font LibertinusMath-Regular:mode=base;!\n"
        "Missing character: There is no ⨍ in font LibertinusMath-Regular:mode=base;!\n"
        "Missing character: There is no ᗮ (U+15EE) in font LibertinusSerif-Regular:mode=node;!\n", encoding="utf-8")
    assert log_missing(str(tmp_path), {"ᗮ": 1}) == {"⨍": 2, "ᗮ": 2}
    assert log_missing(str(tmp_path / "none")) == {}


def test_fallback_juliamono():
    from mlhb.fonts import Fallback
    fb = Fallback()
    assert fb.letter("ᗮ") == "J"
    assert fb.apply("x ᗮ") == r"x \hbfb{J}{ᗮ}" and not fb.missing


def test_source_deprecations():
    from mlhb.deprecated import scan_file
    src = '''namespace Set
/-- a docstring with end in it
end -/
@[deprecated (since := "2026-06-03")] alias mem_diff := mem_sdiff
section
@[simp, deprecated mem_union (since := "2026-01-01")]
theorem mem_or : True := trivial
end
@[deprecated (since := "2026-01-01")] alias ⟨foo, bar⟩ := baz
end Set
@[deprecated "Use `E 6` instead" (since := "2026-07-29")]
abbrev E₆ : Nat := 6
-- @[deprecated] alias commented := x
@[deprecated (since := "2026-01-01")] alias _root_.Top.thing := other
'''
    out: dict[str, str] = {}
    scan_file(src, out)
    assert out == {"Set.mem_diff": "mem_sdiff", "Set.mem_or": "mem_union", "Set.foo": "", "Set.bar": "",
                   "E₆": "", "Top.thing": "other"}
