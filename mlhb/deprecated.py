"""The deprecated declarations of the Mathlib source.

The index does not mark each deprecated alias of Mathlib. This module reads the `.lean` files of the Mathlib
source and finds each declaration with the attribute `deprecated`. It gives the full name of the declaration
and its target (the new name), or "" when the attribute has no target.

The parse is simple. It removes the comments, follows `namespace`, `section`, `mutual` and `end` to get the
current namespace, and reads the name after the declaration keyword. A name that starts with `_root_.` has no
namespace. The form `alias ⟨a, b⟩ := c` gives the two names a and b, with no target,
because they are the two directions of the iff c.
"""

from __future__ import annotations

import os
import re

_COMMENT = re.compile(r"/-.*?-/|--[^\n]*", re.S)
_SCOPE = re.compile(r"^(?:noncomputable\s+)?(namespace|section|mutual|end)\b[ \t]*([^\s]*)", re.M)
_DECL = re.compile(
    r"@\[([^\]]*\bdeprecated\b[^\]]*)\]\s*"
    r"(?:(?:protected|private|noncomputable|nonrec|unsafe|partial)\s+)*"
    r"(alias|theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\s+"
    r"(⟨[^⟩]*⟩|[^\s:({\[]+)"
    r"(?:[^\n]*?:=\s*([^\s]+))?")
_TARGET = re.compile(r"\bdeprecated\s+([^\s(\]\"][^\s(\]]*)")


def _names(raw: str) -> list[str]:
    if raw.startswith("⟨"):
        return [n.strip() for n in raw[1:-1].split(",") if n.strip() and n.strip() != "_"]
    return [raw]


def scan_file(text: str, out: dict[str, str]):
    text = _COMMENT.sub(lambda m: re.sub(r"[^\n]", " ", m.group(0)), text)
    events = [(m.start(), "scope", m) for m in _SCOPE.finditer(text)]
    events += [(m.start(), "decl", m) for m in _DECL.finditer(text)]
    events.sort(key=lambda e: e[0])
    stack: list[tuple[str, str]] = []
    for _, kind, m in events:
        if kind == "scope":
            word, arg = m.group(1), m.group(2)
            if word == "end":
                if stack:
                    stack.pop()
            elif word == "namespace":
                stack.append(("ns", arg))
            else:
                stack.append((word, arg))
            continue
        ns = ".".join(a for k, a in stack if k == "ns" and a)
        t = _TARGET.search(m.group(1))
        alias = m.group(2) == "alias" and not m.group(3).startswith("⟨")   # ⟨a, b⟩ are the two directions
        target = t.group(1) if t else (m.group(4) or "" if alias else "")
        for n in _names(m.group(3)):
            if n.startswith("_root_."):
                full = n[len("_root_."):]
            else:
                full = f"{ns}.{n}" if ns else n
            out[full] = target


def scan(src: str) -> dict[str, str]:
    """The deprecated declarations of the `.lean` files under src: full name to target."""
    out: dict[str, str] = {}
    for d, _, files in os.walk(src):
        for f in files:
            if f.endswith(".lean"):
                with open(os.path.join(d, f), encoding="utf-8", errors="replace") as h:
                    text = h.read()
                if "deprecated" in text:
                    scan_file(text, out)
    return out


def source_dir(lean_root: str) -> str:
    """The Mathlib source of the companion, or "" when it is not there."""
    p = os.path.join(lean_root, ".lake", "packages", "mathlib", "Mathlib")
    return p if os.path.isdir(p) else ""
