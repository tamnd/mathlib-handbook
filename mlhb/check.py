"""The checks of `mlhb check` (spec 12.3).

A fault fails the check:
1. a bad front matter (no title, no kind, no status, a status that is not of 07.8, no drafted_by, the status
   reviewed with an empty reviewed_by, a kind that is not of 07.4), a section that does not open with a ##
   heading, a missing part or a wrong order of parts (07.3, 07.4), a Reference part without <?reference?>;
2. a Lean name in a Mathlib box, a <?decl?> or an explains list that is not in the index;
3. a deprecated name, with the new name in the message, unless the section is stale;
4. a <?lean?> anchor that is not in the companion;
5. a module in modules whose home volume is another volume;
6. a declaration at E3 or E2 in the explains of two sections;
7. a requires id that does not exist, or a cycle of requires;
8. a reads_with key that is not in books/;
9. an en dash, an em dash, the word "we" and the banned words in the prose, and an exercise with no grade (A),
   (B), (C) or (L).

The checks 2 and 3 run only with an index (--index), and the check 4 only with the companion (--lean).

A warning does not fail the check: a theory, api or tactic section with fewer than 4 or more than 12
exercises, a theory section whose Examples part has fewer than 2 examples, and a section with no mathlib commit.
"""

from __future__ import annotations

import os
import re

from .content import KINDS, STATUSES, Section, Volume, front, read
from .map import Map
from .md import _FENCE, BOX_CLOSE, BOX_HEAD, BOX_OPEN
from .resolve import directives

BANNED = (r"\b(leverag(?:e|es|ed|ing)|showcas(?:e|es|ed|ing)|powerful|elegant(?:ly)?|seamless(?:ly)?|crucial(?:ly)?|"
          r"delv(?:e|es|ed|ing)|journey|landscape|tapestry|realm|intricate|pivotal|robust|underscores?|"
          r"notably|furthermore|moreover|we)\b")

PARTS = ("Overview", "Definitions", "Theorems and proofs", "Examples", "The library around it", "Exercises",
         "Notes and history", "Reference")
TACTIC = ("Overview", "What it does", "How to use it", "What it cannot do", "Examples", "Exercises", "Reference")

# The order of the parts of each kind, and the parts that a section of the kind must have (07.4).
ORDER = {"theory": PARTS, "api": PARTS, "instance": PARTS, "tactic": TACTIC, "survey": PARTS}
NEED = {
    "theory": PARTS,
    "api": ("Overview", "The library around it", "Exercises", "Reference"),
    "instance": ("Overview", "Theorems and proofs", "Examples", "Reference"),
    "tactic": TACTIC,
    "survey": ("Overview", "Notes and history"),
}

_GRADE = re.compile(r"^\d+\.\s+\((A|B|C|L)\)\s")
_REQ = re.compile(r"^(V[0-9]{2})(?:\.(C[0-9]{2}))?$")


def _prose(t: str) -> str:
    p = re.sub(r"```.*?```|~~~.*?~~~|\$\$.*?\$\$|\$[^$\n]*\$|`[^`\n]*`|<\?.*?\?>", " ", t, flags=re.S)
    return re.sub(r"\]\([^)]*\)", "]", p)


def style(rel: str, text: str, faults: list[str]):
    prose = _prose(text)
    for w in sorted({w.lower() for w in re.findall(BANNED, prose, flags=re.I)}):
        faults.append(f"{rel}: style: the word '{w}'")
    if re.search("[\u2013\u2014]", prose):
        faults.append(f"{rel}: style: an en dash or an em dash")


def headings(body: str) -> list[tuple[int, int, str]]:
    """The headings of a body outside code: (line index, level, text)."""
    out, fence = [], None
    for i, ln in enumerate(body.split("\n")):
        f = _FENCE.match(ln)
        if f:
            fence = None if fence == f.group(1)[0] else (fence or f.group(1)[0])
            continue
        if fence:
            continue
        m = re.match(r"^(#{1,6}) +(.*?)\s*$", ln)
        if m:
            out.append((i, len(m.group(1)), m.group(2)))
    return out


def parts(rel: str, kind: str, body: str, faults: list[str]):
    order = ORDER.get(kind)
    if not order:
        return
    found = [t for _, lv, t in headings(body) if lv == 3 and t in order]
    for p in NEED[kind]:
        if p not in found:
            faults.append(f"{rel}: a {kind} section has no part '### {p}'")
    idx = [order.index(t) for t in found]
    if idx != sorted(idx) or len(set(found)) != len(found):
        faults.append(f"{rel}: the parts are not in the order {', '.join(p for p in order if p in found)}")
    if "Reference" in found and not any(k == "reference" for _, k, _ in directives(body)):
        faults.append(f"{rel}: the part Reference has no <?reference?>; the builder writes the table")


def part_text(body: str, name: str) -> str:
    """The text of the ### part `name`, up to the next heading of level 3 or less."""
    lines = body.split("\n")
    hs = headings(body)
    for n, (i, lv, t) in enumerate(hs):
        if lv == 3 and t == name:
            end = next((j for j, lv2, _ in hs[n + 1:] if lv2 <= 3), len(lines))
            return "\n".join(lines[i + 1:end])
    return ""


def exercises(body: str, whole: bool = False) -> list[tuple[int, str]]:
    """The numbered items under an Exercises or Problems heading (or in all of `body` when `whole`)."""
    out, fence, inside = [], None, whole
    for i, ln in enumerate(body.split("\n")):
        f = _FENCE.match(ln)
        if f:
            fence = None if fence == f.group(1)[0] else (fence or f.group(1)[0])
            continue
        if fence:
            continue
        m = re.match(r"^(#{1,6}) +(.*?)\s*$", ln)
        if m:
            inside = whole or m.group(2).strip() in ("Exercises", "Problems")
            continue
        if inside and re.match(r"^\d+\.\s", ln):
            out.append((i, ln))
    return out


def grades(rel: str, body: str, offset: int, faults: list[str], whole: bool = False) -> int:
    items = exercises(body, whole)
    for i, ln in items:
        if not _GRADE.match(ln):
            faults.append(f"{rel}:{i + offset}: an exercise with no grade (A), (B), (C) or (L)")
    return len(items)


def box_names(body: str) -> list[tuple[int, str, str]]:
    """The Lean names of a body in the first line of a Mathlib box: (line index, name, module)."""
    out, fence, box, head = [], None, False, False
    for i, ln in enumerate(body.split("\n")):
        f = _FENCE.match(ln)
        if f:
            fence = None if fence == f.group(1)[0] else (fence or f.group(1)[0])
            continue
        if fence:
            continue
        if not box and BOX_OPEN.match(ln):
            box = head = True
            continue
        if box and BOX_CLOSE.match(ln):
            box = head = False
            continue
        if box and head and ln.strip():
            head = False
            m = BOX_HEAD.match(ln.strip())
            if m:
                out.append((i, m.group(1), m.group(2)))
    return out


class Checker:
    def __init__(self, smap: Map, root: str, all_volumes: list[Volume]):
        self.map = smap
        self.root = root
        self.faults: list[str] = []
        self.warns: list[str] = []
        # the ids that requires can name: the volumes and chapters of the map and of the content
        self.vols = set(smap.volumes) | {v.id for v in all_volumes}
        self.chapters = {f"{v.id}.{c.id}" for v in all_volumes for c in v.chapters}
        for vid in smap.plans:
            self.chapters |= smap.chapter_ids(vid)
        self.home: dict[str, str] = {}          # an E3 or E2 name: its section id
        self.graph: dict[str, set[str]] = {}    # a chapter id: the chapter ids it requires

    def rel(self, p: str) -> str:
        return os.path.relpath(p, self.root)

    def name(self, rel: str, where: str, n: str, sec: Section):
        """Checks 2 and 3 for one Lean name."""
        if self.map.decls is None:
            return
        d = self.map.decls.get(n)
        if d is None:
            self.faults.append(f"{rel}: {where}: {n} is not in the index")
        elif d.deprecated is not None and sec.status != "stale":
            new = f"; use {d.deprecated}" if d.deprecated else ""
            self.faults.append(f"{rel}: {where}: {n} is deprecated{new}")

    def section(self, v: Volume, ch, s: Section):
        rel = self.rel(s.path)
        text = read(s.path)
        fm, body = front(text)
        offset = text[:len(text) - len(body)].count("\n") + 1
        f = self.faults
        # 1. the front matter and the parts
        for k in ("title", "kind", "status", "drafted_by"):
            if not fm.get(k):
                f.append(f"{rel}: the front matter has no {k}")
        if s.kind and s.kind not in KINDS:
            f.append(f"{rel}: the kind '{s.kind}' is not one of {', '.join(KINDS)}")
        if fm.get("status") and s.status not in STATUSES:
            f.append(f"{rel}: the status '{s.status}' is not one of {', '.join(STATUSES)}")
        if s.status == "reviewed" and not fm.get("reviewed_by"):
            f.append(f"{rel}: the status is reviewed and reviewed_by is empty")
        if not re.match(r"\s*## ", body):
            f.append(f"{rel}: a section must open with a ## heading")
        parts(rel, s.kind, body, f)
        if not fm.get("mathlib") and s.status != "planned":
            self.warns.append(f"{rel}: the front matter has no mathlib commit")
        # 2 and 3. the names
        for i, n, _ in box_names(body):
            self.name(rel, f"line {i + offset}, Mathlib box", n, s)
        for depth, names in s.explains.items():
            for n in names:
                self.name(rel, f"explains {depth}", n, s)
                if depth in ("E3", "E2"):   # 6. one home section for each E3 and E2 name
                    other = self.home.setdefault(n, s.id)
                    if other != s.id:
                        f.append(f"{rel}: {n} is at {depth} in this section and in the section {other}")
        for i, kind, arg in directives(body):
            if kind == "decl":
                self.name(rel, f"line {i + offset}, <?decl?>", arg, s)
            elif kind == "lean" and self.map.lean_root:   # 4. the anchors
                try:
                    self.map.lean_anchor(arg)
                    if self.map.highlight is not None:
                        self.map.highlight.anchor(arg)
                except KeyError as e:
                    f.append(f"{rel}:{i + offset}: <?lean {arg}?>: {e.args[0]}")
        # 5. the home volume of each module
        for m in s.modules:
            home = self.map.module_home.get(m)
            if home and home != v.id:
                f.append(f"{rel}: the module {m} has its home in {home}, not in {v.id}")
        # 7. requires
        me = f"{v.id}.{ch.id}"
        for r in s.requires:
            m = _REQ.match(r)
            if not m or (m.group(2) is None and r not in self.vols) or (m.group(2) and r not in self.chapters):
                f.append(f"{rel}: the requires id '{r}' does not exist")
            elif m.group(2):
                self.graph.setdefault(me, set()).add(r)
        # 8. reads_with
        for r in s.reads_with:
            key = r.strip().split()[0] if r.strip() else ""
            if key not in self.map.books:
                f.append(f"{rel}: the reads_with key '{key}' is not in books/")
        # 9. the style and the grades
        style(rel, body, f)
        n_ex = grades(rel, body, offset, f)
        if s.kind in ("theory", "api", "tactic") and not 4 <= n_ex <= 12:
            self.warns.append(f"{rel}: a {s.kind} section with {n_ex} exercises (07.3 asks for 4 to 12)")
        if s.kind == "theory":
            ex = part_text(body, "Examples")
            n = len(re.findall(r"^\*\*(?:Example|Counterexample)\b", ex, flags=re.M))
            if n < 2:
                self.warns.append(f"{rel}: the part Examples has {n} examples (07.3 asks for at least 2)")

    def volume(self, v: Volume):
        vrel = self.rel(v.dir)
        vy = os.path.join(v.dir, "volume.yaml")
        if not os.path.exists(vy):
            self.faults.append(f"{vrel}: no volume.yaml")
        else:
            if not v.meta.get("title"):
                self.faults.append(f"{vrel}/volume.yaml: no title")
            mv = self.map.volumes.get(v.id)
            if mv and str(mv.get("title") or "") != str(v.meta.get("title") or ""):
                self.faults.append(f"{vrel}/volume.yaml: the title is not the title of {v.id} in "
                                   f"blueprint/volumes.yaml ({mv.get('title')})")
        for p in [os.path.join(v.dir, "intro.md")] + [os.path.join(c.dir, "intro.md") for c in v.chapters]:
            if os.path.exists(p):
                style(self.rel(p), front(read(p))[1], self.faults)
        for ch in v.chapters:
            pp = os.path.join(ch.dir, "problems.md")
            if os.path.exists(pp):
                text = read(pp)
                _, pbody = front(text)
                style(self.rel(pp), pbody, self.faults)
                grades(self.rel(pp), pbody, text[:len(text) - len(pbody)].count("\n") + 1, self.faults, whole=True)
            for s in ch.sections:
                self.section(v, ch, s)

    def cycles(self):
        """7. A cycle of requires between chapters."""
        state: dict[str, int] = {}
        stack: list[str] = []

        def visit(n: str):
            state[n] = 1
            stack.append(n)
            for m in sorted(self.graph.get(n, ())):
                if state.get(m) == 1:
                    cyc = stack[stack.index(m):] + [m]
                    self.faults.append(f"requires: a cycle {' -> '.join(cyc)}")
                elif not state.get(m):
                    visit(m)
            stack.pop()
            state[n] = 2

        for n in sorted(self.graph):
            if not state.get(n):
                visit(n)


def check(volumes: list[Volume], smap: Map, root: str, all_volumes: list[Volume] | None = None
          ) -> tuple[list[str], list[str]]:
    c = Checker(smap, root, all_volumes or volumes)
    if not smap.exists:
        c.faults.append(f"the map is not found at {smap.root} (give it with --map PATH)")
    for v in volumes:
        c.volume(v)
    c.cycles()
    return c.faults, c.warns
