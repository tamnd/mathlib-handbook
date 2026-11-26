"""The volumes of the handbook and the Markdown of each.

A volume is content/<NN-slug>/. Its Markdown is the volume intro.md (if any), then each chapter: a # heading with
the number of the chapter, a Draft mark when the chapter is not reviewed, the chapter intro.md, its sections with
the directives resolved (12.4) and with numbered headings and statements, the problems.md of the chapter (if any),
and the list of the books that its sections read with.
"""

from __future__ import annotations

import os
import re

from . import content
from .content import Chapter, Volume
from .map import Map
from .md import Converter
from .resolve import resolve


def reads_key(r: str) -> str:
    """The book key of a reads_with entry: "Rud76 §2.C" gives Rud76."""
    return r.strip().split()[0] if r.strip() else ""


class Book:
    def __init__(self, content_dir: str, map_dir: str, index: str = "", lean: str = "", pin: str = ""):
        self.content = content_dir
        self.map = Map.load(map_dir, os.path.join(os.path.dirname(os.path.abspath(content_dir)), "books"),
                            index, lean)
        self.volumes = content.load(content_dir)
        self.map_commit = self.map.commit() or pin or "unknown"

    def volume(self, n) -> Volume:
        """The volume with the label or the id `n`: 13, "13" or "V13"."""
        want = str(n).strip().upper()
        for v in self.volumes:
            if want in (v.id, v.label, v.dirname[:2]):
                return v
        raise KeyError(n)

    def markdown(self, v: Volume) -> tuple[str, dict]:
        conv = Converter(self.map)
        out = []
        pre = v.id.lower()
        if v.intro.strip():
            out.append(f"# Introduction {{#{pre}-intro}}\n")
            out.append(conv.page(v.intro, shift=0, prefix=f"{pre}-intro"))
        for ch in v.chapters:
            out.append(self._chapter(v, ch, conv))
        md = "\n\n".join(out)
        stats = {"words": len(re.findall(r"\b\w+\b", md)), "boxes": len(conv.names),
                 "chapters": len(v.chapters), "drafts": sum(1 for c in v.chapters if c.draft),
                 "lean": sorted(set(conv.names))}
        return md, stats

    def _chapter(self, v: Volume, ch: Chapter, conv: Converter) -> str:
        n = str(ch.num)
        prefix = f"{v.id.lower()}-c{ch.num}"
        out = [f"# {conv.inline(ch.title)} {{#{prefix} num=\"{n}\"}}\n"]
        if ch.draft:
            out.append(draft_mark(ch.status))
        if ch.intro.strip():
            out.append(conv.page(ch.intro, shift=0, prefix=prefix))
        if ch.sections:
            text = "\n\n".join(resolve(self.map, v, s, s.body).strip("\n") for s in ch.sections)
            out.append(conv.page(text, shift=0, prefix=prefix, numbering=n, items=v.item_prefix))
        if ch.problems.strip():
            out.append(conv.page(ch.problems, shift=0, prefix=f"{prefix}-problems"))
        refs = self._references(ch)
        if refs:
            out.append(f"## Books {{#{prefix}-books}}\n")
            out.append("\n".join(refs) + "\n")
        return "\n\n".join(out)

    def _references(self, ch: Chapter) -> list[str]:
        keys: list[str] = []
        for s in ch.sections:
            for k in map(reads_key, s.reads_with):
                if k and k not in keys:
                    keys.append(k)
        out = []
        for k in keys:
            b = self.map.books.get(k)
            out.append(f"- **{k}**. {b.cite()}" if b else f"- **{k}**.")
        return out


def draft_mark(status: str) -> str:
    """The mark at the start of a chapter that is not reviewed: a box in the PDF and in the EPUB."""
    return (f"::: {{.draft latex-env=\"hbdraft\"}}\n**Draft.** The status of this chapter is {status}. "
            "No person has reviewed it yet, and it can contain errors.\n:::\n")


def out_name(v: Volume, version: str, tag: str = "") -> str:
    """mathlib-handbook-<NN-slug>-<version>+mathlib-<tag> (12.6). With no tag, the name has no +mathlib part."""
    name = f"mathlib-handbook-{v.dirname}-{version}"
    return f"{name}+mathlib-{tag}" if tag else name
