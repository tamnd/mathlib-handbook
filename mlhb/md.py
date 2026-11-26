"""The conversion of the Markdown of a chapter into the Markdown of a volume.

Each ## heading of a chapter gets a number (5.3). Each bold statement head gets the number of its volume, its
chapter and its place in the chapter: in Volume 13, **Theorem (Heine-Borel).** becomes Theorem 13.5.2
(Heine-Borel) when it is item 2 of chapter 5.

A Mathlib box (spec 07.5) is the fenced div `::: mathlib`. Its first line gives the Lean name and the module in
code spans. The builder makes the name a link to the declaration page of the site and the module a link to the
Mathlib documentation. Another code span in the box that is a name of the index also becomes a link. A link to a
path of the site (/decl/Name/) becomes a link to https://mathlib.tamnd.com.
"""

from __future__ import annotations

import re

from .content import anchor
from .map import SITE, Map, decl_url, docs_url

KINDS = "Definition|Theorem|Proposition|Lemma|Corollary|Example|Counterexample|Remark"

_FENCE = re.compile(r"^(`{3,}|~{3,})")
_MATH = re.compile(r"\$\$.*?\$\$|(?<![\\$])\$[^$\n]+\$", re.S)
_LINK = re.compile(r"(?<!!)\[((?:[^\[\]]|\[[^\]]*\])*)\]\(([^)\s]+)\)")
_STMT = re.compile(r"^\*\*(" + KINDS + r")((?: [a-z]+)?)(?: [0-9]+(?:\.[0-9]+)*)?((?: \((?:[^()]|\([^()]*\))*\))?)\.\*\*")
BOX_OPEN = re.compile(r"^:::+\s*\{?\s*\.?mathlib\s*\}?\s*$")
BOX_CLOSE = re.compile(r"^:::+\s*$")
# `Name` · `Module`, the first line of a Mathlib box
BOX_HEAD = re.compile(r"^`([^`\s]+)`\s*·\s*`([^`\s]+)`\s*$")


def label_id(*parts: str) -> str:
    return "-".join(p for p in parts if p).replace("_", "-").replace(".", "-")


class Converter:
    """Converts the Markdown of one chapter for one volume."""

    def __init__(self, smap: Map):
        self.map = smap
        self.names: list[str] = []     # the Lean names of the Mathlib boxes, in order

    def resolve(self, dest: str, text: str) -> str:
        if dest.startswith("/") and not dest.startswith("//"):
            return f"[{text}]({SITE}{dest})"
        return f"[{text}]({dest})"

    def inline(self, s: str, box: bool = False) -> str:
        """Links in one line of prose, outside code and mathematics. In a Mathlib box, a code span that is a
        name of the index becomes a link to its declaration page."""
        keep: list[str] = []

        def hold(m: re.Match | str) -> str:
            keep.append(m if isinstance(m, str) else m.group(0))
            return f"\x00{len(keep) - 1}\x00"

        def code(m: re.Match) -> str:
            name = m.group(0)[1:-1]
            if box and self.map.decls is not None and name in self.map.decls:
                keep.append(f"[{m.group(0)}]({decl_url(name)})")
            else:
                keep.append(m.group(0))
            return f"\x00{len(keep) - 1}\x00"

        if box:   # a link that the writer typed keeps its text: no second link inside it
            s = _LINK.sub(lambda m: hold(self.resolve(m[2], m[1])), s)
        s = re.sub(r"`[^`\n]*`", code, s)
        s = _MATH.sub(hold, s)
        s = _LINK.sub(lambda m: self.resolve(m[2], m[1]), s)
        while "\x00" in s:
            s = re.sub(r"\x00(\d+)\x00", lambda m: keep[int(m[1])], s)
        return s

    def box_head(self, name: str, module: str) -> str:
        """The first line of a Mathlib box as the book prints it."""
        self.names.append(name)
        return (f"[[`{name}`]({decl_url(name)}) · [`{module}`]({docs_url(module, name)})]"
                f"{{.mathlib-head latex-cmd=\"hblean\"}}")

    def page(self, md: str, *, shift: int, prefix: str, numbering: str | None = None, items: str = "") -> str:
        """Convert a page. `shift` moves every heading down (## becomes ### for shift 1). Headings get the
        identifier `prefix-<anchor>`. With `numbering` ("3"), each ## heading gets a number 3.1, 3.2, and each
        bold statement head the number `items` + chapter + its place in the chapter: with items "13.",
        Definition 13.3.5 is item 5 of chapter 3."""
        out, fence = [], None
        sec = stmt = 0
        box = False        # inside a Mathlib box
        head = False       # the next line with text is the first line of the box
        for ln in md.split("\n"):
            f = _FENCE.match(ln)
            if f:
                fence = None if fence == f.group(1)[0] else (fence or f.group(1)[0])
                out.append(ln)
                continue
            if fence:
                out.append(ln)
                continue
            if not box and BOX_OPEN.match(ln):
                box = head = True
                out.append("::: {.mathlib latex-env=\"hbmathlib\"}")
                continue
            if box and BOX_CLOSE.match(ln):
                box = head = False
                out.append(":::")
                continue
            if box and head and ln.strip():
                head = False
                bm = BOX_HEAD.match(ln.strip())
                if bm:
                    out.append(self.box_head(bm.group(1), bm.group(2)))
                    continue
            m = re.match(r"^(#{1,6}) +(.*?)\s*$", ln)
            if m:
                level = len(m.group(1))
                title = m.group(2)
                lab = label_id(prefix, anchor(title))
                if level > 2 and sec:   # a subsection: its anchor has the number of its section, so that each is unique
                    lab = label_id(prefix, str(sec), anchor(title))
                hd = "#" * min(6, level + shift)
                if numbering and level == 2:
                    sec += 1
                    out.append(f"{hd} {self.inline(title)} {{#{lab} num=\"{numbering}.{sec}\"}}")
                else:
                    out.append(f"{hd} {self.inline(title)} {{#{lab}}}")
                continue
            m = _STMT.match(ln)
            if m and numbering:
                stmt += 1
                kind, more, name = m.group(1), m.group(2), m.group(3)
                num = f"{items}{numbering}.{stmt}"
                rest = ln[m.end():]
                lab = label_id(prefix, "st", str(stmt))
                hd = f"[{kind}{more} {num}{self.inline(name)}.]{{latex-cmd=\"hbsthead\"}}"
                if not out or not out[-1].strip():   # a paragraph of its own: a little space above it
                    out.append("```{=latex}\n\\hbstskip\\hbnoindentnext\n```\n")
                out.append(f"[]{{#{lab}}}{hd}{self.inline(rest)}")
                continue
            out.append(self.inline(ln, box))
        return "\n".join(out)
