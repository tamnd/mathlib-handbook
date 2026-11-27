"""The Catalogue volumes (spec 06.4 of tamnd/mathlib).

`mlib catalogue` of tamnd/mathlib-agent writes one file C<NN>.jsonl.gz for each main volume. The first line is a
header. Each other line is one declaration whose home is in the main volume, in module order:

    {"name": "...", "kind": "theorem", "module": "Mathlib.Topology.Basic", "attrs": ["simp"], "depth": "E1",
     "source": "E1", "text": "...", "family": "F-ext", "section": "V13.C01.S02"}

The source of the sentence is E1 (a checked informal record), family (the text of the E0 family), doc (the first
sentence of the docstring of Mathlib) or none. The PDF is in small type in two columns. The EPUB is a list.
"""

from __future__ import annotations

import gzip
import json
import os
import re
import shutil
import subprocess
import time

from .fonts import Fallback
from .latex import break_names, log_missing, run_tex
from .paths import ROOT
from .util import volume_hue

_SPECIAL = {"\\": r"\textbackslash{}", "{": r"\{", "}": r"\}", "$": r"\$", "&": r"\&", "#": r"\#",
            "^": r"\textasciicircum{}", "_": r"\_", "%": r"\%", "~": r"\textasciitilde{}"}

SOURCES = ("E1", "family", "doc", "none")


def title(h: dict) -> str:
    """Catalogue of General topology; a title that starts with The gets a small t: Catalogue of the tactics of Mathlib."""
    t = str(h.get("title", ""))
    return "Catalogue of " + (t[0].lower() + t[1:] if t.startswith("The ") else t)


def load(path: str) -> tuple[dict, list[dict]]:
    with gzip.open(path, "rt", encoding="utf-8") as f:
        header = json.loads(f.readline())
        rows = [json.loads(line) for line in f if line.strip()]
    if "catalogue" not in header:
        raise ValueError(f"{path} has no Catalogue header")
    return header, rows


def esc(s: str) -> str:
    return "".join(_SPECIAL.get(c, c) for c in s)


def text_tex(s: str) -> str:
    """The sentence as LaTeX. A code span is in the monospace font. Markdown marks for bold and italic and the
    dollar signs of mathematics in a docstring go away, so the text prints as plain words."""
    out = []
    for i, part in enumerate(s.split("`")):
        if i % 2:
            out.append(r"\texttt{" + esc(part) + "}")
        else:
            part = re.sub(r"\*\*|__|(?<!\w)\*(?=\S)|(?<=\S)\*(?!\w)", "", part).replace("$", "")
            out.append(esc(part))
    return "".join(out)


def text_md(s: str) -> str:
    """The sentence as Markdown for the EPUB, with the dollar signs of a docstring removed."""
    parts = s.split("`")
    return "`".join(p if i % 2 else p.replace("$", "").replace("\\", "\\\\") for i, p in enumerate(parts))


def meta(r: dict) -> str:
    bits = [r.get("kind", "")]
    attrs = [a for a in r.get("attrs") or [] if a != r.get("kind")]
    if attrs:
        bits.append(", ".join(attrs))
    if r.get("depth"):
        bits.append(r["depth"])
    if r.get("section"):
        bits.append(r["section"])
    return " · ".join(b for b in bits if b)


def families(rows: list[dict]) -> list[tuple[str, str, int]]:
    """The E0 families of the rows with a family sentence: (id, text, members), in the order of first use."""
    seen: dict[str, list] = {}
    for r in rows:
        if r.get("source") == "family":
            f = seen.setdefault(r["family"], [r.get("text") or "", 0])
            f[1] += 1
    return [(k, v[0], v[1]) for k, v in seen.items()]


def row_text(r: dict) -> str:
    """The sentence of a row. A family row gives the id of the family: the preface gives its sentence."""
    if r.get("source") == "family":
        return f"Family {r['family']}."
    return r.get("text") or ""


def preface(h: dict) -> str:
    n = max(h.get("count", 0), 1)
    src = h.get("sources") or {}
    pct = {k: f"{src.get(k, 0):,} ({100 * src.get(k, 0) / n:.1f}%)" for k in SOURCES}
    return (f"This Catalogue lists the {h.get('count', 0):,} declarations whose home is in Volume "
            f"{int(h['volume'][1:])}, in module order. The deprecated aliases are not in the list. Each entry gives "
            "the Lean name, then the kind, the attributes, the depth and the home section in the plan of the volume, "
            "then one sentence. The sentence comes from the first source that has one. An E1 sentence comes from an "
            f"informal record that passed its checks: {pct['E1']}. A member of an E0 family gives the id of the family after its "
            f"facts, and the list below gives the sentence of each family: {pct['family']}. A docstring sentence is the first sentence of the docstring of Mathlib, "
            f"and the entry has the mark doc: {pct['doc']}. The other entries have no sentence yet: {pct['none']}.")


def latex_body(h: dict, rows: list[dict]) -> str:
    fams = "".join(r"\hbcatfamily{" + esc(k) + "}{" + text_tex(t) + "}{" + f"{n:,}" + "}" for k, t, n in families(rows))
    out = [r"\hbcatpreface{" + esc(preface(h)) + "}{" + fams + "}", r"\begin{hbcatlist}"]
    module = None
    for r in rows:
        if r["module"] != module:
            module = r["module"]
            out.append(r"\hbcatmodule{" + r"\texttt{" + esc(module) + "}}")
        src = r.get("source", "none")
        facts = meta(r)
        if src == "family":   # a family row is one line: the id of the family goes with the facts
            facts, text = f"{facts} · {r['family']}", ""
        else:
            text = text_tex(row_text(r))
        if src == "doc":
            text += r" \hbcatdoc"
        out.append(r"\hbcatrow{\texttt{" + esc(r["name"]) + "}}{" + esc(facts) + "}{" + text + "}")
    out.append(r"\end{hbcatlist}")
    return "\n".join(out) + "\n"


def main_tex(h: dict, edition: str, date: str) -> str:
    num = int(h["volume"][1:])
    name = esc(title(h))
    commit = h.get("mathlib", "")[:10]
    summary = esc(f"Every declaration of Mathlib whose home is in Volume {num}, with one sentence for each.")
    return rf"""\documentclass[10pt,twoside,openany]{{book}}
\RequirePackage{{xcolor}}
\definecolor{{hbaccent}}{{HTML}}{{{volume_hue(num)}}}
\usepackage{{handbook}}
\usepackage{{catalogue}}
\renewcommand\hbvolnum{{{h['catalogue']}}}
\renewcommand\hbvolname{{{name}}}
\hypersetup{{pdftitle={{The Mathlib Handbook, {h['catalogue']}: {name}}},pdfauthor={{The mathlib-handbook contributors}}}}
\begin{{document}}
\frontmatter
\hbtitlepage{{{h['catalogue']}}}{{{name}}}{{{summary}}}{{{edition}}}{{{date}}}
\hbcopyright{{{edition}}}{{{date}}}{{{commit}}}{{{h['catalogue']}}}{{{name}}}
\mainmatter
\input{{body.tex}}
\end{{document}}
"""


def build_pdf(h: dict, rows: list[dict], outdir: str, edition: str, date: str) -> dict:
    os.makedirs(outdir, exist_ok=True)
    fb = Fallback()
    body = break_names(fb.apply(latex_body(h, rows)))
    open(os.path.join(outdir, "body.tex"), "w").write(body)
    open(os.path.join(outdir, "main.tex"), "w").write(main_tex(h, edition, date))
    for sty in ("handbook.sty", "catalogue.sty"):
        shutil.copy(os.path.join(ROOT, "tex", sty), outdir)
    shutil.copytree(os.path.join(ROOT, "tex", "fonts"), os.path.join(outdir, "fonts"), dirs_exist_ok=True)
    t = time.time()
    r, passes = run_tex(outdir, max_passes=2)
    info = {"rows": len(rows), "missing_glyphs": log_missing(outdir, fb.missing),
            "tectonic_s": round(time.time() - t, 1), "passes": passes, "ok": r.returncode == 0}
    if r.returncode:
        info["error"] = (r.stdout + r.stderr)[-6000:]
    pdf = os.path.join(outdir, "main.pdf")
    if os.path.exists(pdf):
        info["pdf"] = pdf
        if shutil.which("pdfinfo"):   # the page count is for the log; the CI has no poppler
            out = subprocess.run(["pdfinfo", pdf], capture_output=True, text=True).stdout
            for line in out.splitlines():
                if line.startswith("Pages"):
                    info["pages"] = int(line.split()[-1])
    return info


def epub_md(h: dict, rows: list[dict], edition: str, date: str) -> str:
    num = int(h["volume"][1:])
    q = lambda s: s.replace('"', '\\"')
    out = [f"""---
title:
- type: main
  text: "{q(title(h))}"
- type: subtitle
  text: "The Mathlib Handbook, {h['catalogue']}"
creator:
- role: author
  text: "The mathlib-handbook contributors"
publisher: "mathlib.tamnd.com"
date: "{date}"
lang: en
rights: "Text CC BY 4.0; builder MIT. Edition {edition}, Mathlib commit {h.get('mathlib', '')[:10]}."
...
""", "# About this Catalogue {.unnumbered}\n", preface(h).replace("$", "") + "\n"]
    out += [f"- **{k}** ({n:,} entries). {text_md(t)}" for k, t, n in families(rows)]
    module = None
    for r in rows:
        if r["module"] != module:
            module = r["module"]
            out.append(f"\n# `{module}` {{.unnumbered}}\n")
        text = text_md(row_text(r))
        if r.get("source") == "doc":
            text += " *(doc)*"
        out.append(f"- **`{r['name']}`** *{meta(r)}*. {text}".rstrip())
    return "\n".join(out) + "\n"


def build_epub(h: dict, rows: list[dict], outdir: str, edition: str, date: str) -> dict:
    os.makedirs(outdir, exist_ok=True)
    src = os.path.join(outdir, "epub.md")
    open(src, "w").write(epub_md(h, rows, edition, date))
    out = os.path.join(outdir, "main.epub")
    t = time.time()
    r = subprocess.run(["pandoc", src, "-f", "markdown-auto_identifiers-raw_tex-tex_math_dollars", "-t", "epub3",
                        "-o", out, "--toc", "--toc-depth=1", "--split-level=1",
                        "--css", os.path.join(ROOT, "tex", "epub.css")], capture_output=True, text=True)
    info = {"epub_s": round(time.time() - t, 1), "epub_ok": r.returncode == 0}
    if r.returncode:
        info["error"] = r.stderr[-4000:]
    if os.path.exists(out):
        info["epub"] = out
        info["epub_mb"] = round(os.path.getsize(out) / 1e6, 1)
    return info


def out_name(h: dict, version: str, tag: str = "") -> str:
    """mathlib-handbook-c13-catalogue-of-general-topology-<version>, as the name of a main volume (12.6)."""
    slug = re.sub(r"[^a-z0-9]+", "-", title(h).lower()).strip("-")
    name = f"mathlib-handbook-{h['catalogue'].lower()}-{slug}-{version}"
    return f"{name}+mathlib-{tag}" if tag else name
