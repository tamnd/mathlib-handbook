"""The directives of spec 12.4. Each directive is a line of its own.

    <?decl Name?>          the signature of Name at the commit of the index, as a Lean block
    <?lean path#name?>     the Lean text between the anchors of a file of the companion, as a Lean block
    <?reference?>          the reference table of the section (spec 07.6)
    <?missing?>            the standard results of the volume that Mathlib does not have (the key missing of
                           volume.yaml)

A directive that cannot be resolved is an error, and the build stops. There is no fallback text.

A <?decl?> block and a <?lean?> block print with the token kinds of spec 12.5 (mlhb/lean.py). A <?lean?> block
needs the highlighted files of the companion (--highlight) for this. Without them, it is plain Lean text.
"""

from __future__ import annotations

import re

from . import lean
from .content import Section, Volume, as_list
from .map import Map

DIRECTIVE = re.compile(r"^\s*<\?(decl|lean|reference|missing)(?:\s+(\S+?))?\s*\?>\s*$")
_FENCE = re.compile(r"^(`{3,}|~{3,})")

# The attributes that change how the reader uses a declaration (spec 07.6).
SHOWN_ATTRS = ("simp", "ext", "instance", "continuity", "fun_prop", "measurability", "norm_cast", "push_cast",
               "gcongr", "mono", "positivity", "aesop", "to_additive", "reducible", "coe")

_KIND = {"theorem": "theorem", "def": "def", "abbrev": "abbrev", "instance": "instance", "structure": "structure",
         "class": "class", "inductive": "inductive", "axiom": "axiom", "opaque": "opaque", "ctor": "constructor",
         "recursor": "recursor", "quot": "def"}


class ResolveError(Exception):
    pass


def signature(smap: Map, name: str) -> str:
    if smap.decls is None:
        raise ResolveError(f"<?decl {name}?>: give the index with --index")
    d = smap.decls.get(name)
    if d is None:
        raise ResolveError(f"<?decl {name}?>: {name} is not in the index")
    return lean.block(lean.lex_signature(_KIND.get(d.kind, d.kind), name, d.type, smap.decls), smap.decls)


def lean_block(smap: Map, ref: str) -> str:
    """The Lean text between the anchors of a file of the companion."""
    try:
        if smap.highlight is not None:
            return lean.block(smap.highlight.anchor(ref), smap.decls)
        return "```lean\n" + smap.lean_anchor(ref) + "\n```"
    except KeyError as e:
        raise ResolveError(f"<?lean {ref}?>: {e.args[0]}") from None


def _cell(s: str) -> str:
    return s.replace("|", "\\|").replace("\n", " ").strip()


def reference(smap: Map, vol: Volume, sec: Section) -> str:
    """One row per declaration of the section at depth E1 and higher, and one row per family."""
    if smap.decls is None:
        raise ResolveError("<?reference?>: give the index with --index")
    words = smap.informal(vol.id)
    rows: list[tuple[str, str]] = []
    seen = set()
    for depth in ("E3", "E2", "E1"):
        for n in sec.explains.get(depth, []):
            if n not in seen:
                seen.add(n)
                rows.append((n, depth))
    if sec.e1_auto:
        mods = set(sec.modules)
        for n, d in sorted(smap.decls.items()):
            if d.module in mods and n not in seen and n in words and d.deprecated is None:
                seen.add(n)
                rows.append((n, "E1"))
    out = ["| Lean name | Kind | Statement in words | Depth | Attributes |", "|---|---|---|---|---|"]
    for n, depth in rows:
        d = smap.decls.get(n)
        if d is None:
            raise ResolveError(f"<?reference?>: {n} of explains is not in the index")
        attrs = ", ".join(a for a in d.attrs if a in SHOWN_ATTRS)
        out.append(f"| [`{n}`](/decl/{n}/) | {d.kind} | {_cell(words.get(n, ''))} | {depth} | {attrs} |")
    for fid in sec.families:
        f = smap.families.get(fid)
        text = _cell(str(f.get("text") or "")) if f else ""
        out.append(f"| {fid} | family | {text} | E0 | |")
    if len(out) == 2:
        raise ResolveError("<?reference?>: the section explains no declaration and no family")
    return "\n".join(out)


def missing(vol: Volume) -> str:
    items = as_list(vol.meta.get("missing"))
    if not items:
        raise ResolveError("<?missing?>: volume.yaml has no list missing")
    return "\n".join(f"- {x}" for x in items)


def resolve(smap: Map, vol: Volume, sec: Section, body: str) -> str:
    """Replace the directives of a section body. Raise ResolveError on the first directive that fails."""
    out, fence = [], None
    for i, ln in enumerate(body.split("\n"), 1):
        f = _FENCE.match(ln)
        if f:
            fence = None if fence == f.group(1)[0] else (fence or f.group(1)[0])
        if fence or f:
            out.append(ln)
            continue
        m = DIRECTIVE.match(ln)
        if not m:
            out.append(ln)
            continue
        kind, arg = m.group(1), m.group(2) or ""
        try:
            if kind == "decl":
                out.append(signature(smap, arg))
            elif kind == "lean":
                out.append(lean_block(smap, arg))
            elif kind == "reference":
                out.append(reference(smap, vol, sec))
            else:
                out.append(missing(vol))
        except ResolveError as e:
            raise ResolveError(f"{sec.path}: line {i} of the body: {e}") from None
    return "\n".join(out)


def directives(body: str) -> list[tuple[int, str, str]]:
    """The directives of a body outside code: (line index, kind, argument)."""
    out, fence = [], None
    for i, ln in enumerate(body.split("\n")):
        f = _FENCE.match(ln)
        if f:
            fence = None if fence == f.group(1)[0] else (fence or f.group(1)[0])
            continue
        if fence:
            continue
        m = DIRECTIVE.match(ln)
        if m:
            out.append((i, m.group(1), m.group(2) or ""))
    return out
