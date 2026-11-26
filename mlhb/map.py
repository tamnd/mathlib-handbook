"""The map of tamnd/mathlib, the index of Mathlib and the companion tamnd/mathlib-lean.

The map (--map, default ../mathlib):

    blueprint/volumes.yaml        the volumes: id, title, level, prefixes
    blueprint/sections/<V>.yaml   the section plan of a volume: chapters and sections with their ids
    blueprint/families.yaml       the E0 families: id, pattern, text
    records/modules.json          the home volume of each module
    informal/<V>.jsonl            the E1 records: one sentence for each declaration

The folder books/ of the handbook holds the book records that reads_with names: key, title, authors, year.

The index (--index, optional) is the file index.jsonl.gz that mathlib-lean writes, or a folder that has it. It
gives the name, kind, module, type, attributes and the deprecated target of each declaration. With no index, the
checks of the names do not run and a build with a <?decl?> stops.

The companion (--lean, default ../mathlib-lean) holds the Lean files. A <?lean path#name?> directive takes the
text between the lines `-- anchor: name` and `-- end: name` of the file (spec 10.3).
"""

from __future__ import annotations

import glob
import gzip
import json
import os
import re
import subprocess
from dataclasses import dataclass, field

import yaml

from .content import read

SITE = "https://mathlib.tamnd.com"
DOCS = "https://leanprover-community.github.io/mathlib4_docs"


def decl_url(name: str) -> str:
    """The declaration page of the site (spec 13)."""
    return f"{SITE}/decl/{name}/"


def docs_url(module: str, name: str) -> str:
    """The page of the declaration in the Mathlib documentation."""
    return f"{DOCS}/{module.replace('.', '/')}.html#{name}"


def commit(path: str) -> str:
    try:
        return subprocess.run(["git", "-C", path, "rev-parse", "HEAD"], capture_output=True, text=True,
                              check=True).stdout.strip()
    except Exception:
        return ""


@dataclass
class Decl:
    name: str
    kind: str
    module: str
    type: str = ""
    attrs: list[str] = field(default_factory=list)
    deprecated: str | None = None   # the target of a deprecated alias; "" when the alias has no target


@dataclass
class Book:
    key: str
    title: str
    authors: list
    year: str

    def cite(self) -> str:
        """One line of a list of references, in Markdown."""
        bits = []
        if self.authors:
            bits.append(", ".join(str(a) for a in self.authors))
        bits.append(f"*{self.title}*")
        if self.year:
            bits.append(str(self.year))
        return ". ".join(b.rstrip(".") for b in bits if b) + "."


def load_index(path: str) -> tuple[dict[str, Decl], str]:
    """Read index.jsonl.gz (or the folder that has it). Give the declarations and the Mathlib commit."""
    if os.path.isdir(path):
        path = os.path.join(path, "index.jsonl.gz")
    opener = gzip.open if path.endswith(".gz") else open
    out: dict[str, Decl] = {}
    mathlib = ""
    with opener(path, "rt", encoding="utf-8") as f:
        for n, line in enumerate(f):
            r = json.loads(line)
            if n == 0 and "index" in r:
                mathlib = str(r.get("mathlib") or "")
                continue
            attrs, dep = [], None
            for a in r.get("attrs") or []:
                if isinstance(a, str):
                    attrs.append(a)
                elif isinstance(a, dict) and "deprecated" in a:
                    dep = str((a["deprecated"] or {}).get("target") or "")
            out[r["name"]] = Decl(r["name"], str(r.get("kind") or ""), str(r.get("module") or ""),
                                  str(r.get("type") or ""), attrs, dep)
    return out, mathlib


@dataclass
class Map:
    root: str
    volumes: dict[str, dict] = field(default_factory=dict)        # V13: {title, level, prefixes}
    plans: dict[str, dict] = field(default_factory=dict)          # V13: blueprint/sections/V13.yaml
    families: dict[str, dict] = field(default_factory=dict)       # F-map-op: {pattern, text}
    module_home: dict[str, str] = field(default_factory=dict)     # Mathlib.Topology.Basic: V13
    books: dict[str, Book] = field(default_factory=dict)
    decls: dict[str, Decl] | None = None                          # None: no index
    index_commit: str = ""
    lean_root: str = ""
    _informal: dict[str, dict[str, str]] = field(default_factory=dict)

    @property
    def exists(self) -> bool:
        return os.path.exists(os.path.join(self.root, "blueprint", "volumes.yaml"))

    @classmethod
    def load(cls, root: str, books: str = "", index: str = "", lean: str = "") -> "Map":
        m = cls(root, lean_root=lean)
        vp = os.path.join(root, "blueprint", "volumes.yaml")
        if os.path.exists(vp):
            for v in (yaml.safe_load(read(vp)) or {}).get("volumes") or []:
                m.volumes[str(v["id"])] = v
        for p in sorted(glob.glob(os.path.join(root, "blueprint", "sections", "V*.yaml"))):
            y = yaml.safe_load(read(p)) or {}
            m.plans[str(y.get("volume") or os.path.basename(p)[:-5])] = y
        fp = os.path.join(root, "blueprint", "families.yaml")
        if os.path.exists(fp):
            for f in yaml.safe_load(read(fp)) or []:
                m.families[str(f["id"])] = f
        mp = os.path.join(root, "records", "modules.json")
        if os.path.exists(mp):
            for r in json.loads(read(mp)):
                if r.get("volume"):
                    m.module_home[str(r["module"])] = str(r["volume"])
        if books:
            for p in sorted(glob.glob(os.path.join(books, "*.yaml"))):
                y = yaml.safe_load(read(p)) or {}
                key = str(y.get("key") or os.path.basename(p)[:-5])
                m.books[key] = Book(key, str(y.get("title") or key), list(y.get("authors") or []),
                                    str(y.get("year") or ""))
        if index:
            m.decls, m.index_commit = load_index(index)
        return m

    def commit(self) -> str:
        return commit(self.root)

    def chapter_ids(self, vol: str) -> set[str]:
        """The chapter ids of the plan of a volume: V13.C01 and so on."""
        return {f"{vol}.{c['id']}" for c in (self.plans.get(vol) or {}).get("chapters") or []}

    def section_ids(self, vol: str) -> set[str]:
        return {str(s["id"]) for c in (self.plans.get(vol) or {}).get("chapters") or []
                for s in c.get("sections") or []}

    def plan_section(self, sid: str) -> tuple[dict, dict] | None:
        """The chapter and the section of the plan with the id V13.C05.S02."""
        for c in (self.plans.get(sid[:3]) or {}).get("chapters") or []:
            for s in c.get("sections") or []:
                if s.get("id") == sid:
                    return c, s
        return None

    def informal(self, vol: str) -> dict[str, str]:
        """The E1 text of each declaration of a volume, from informal/<vol>.jsonl."""
        if vol not in self._informal:
            out = {}
            p = os.path.join(self.root, "informal", f"{vol}.jsonl")
            if os.path.exists(p):
                for line in read(p).splitlines():
                    if line.strip():
                        r = json.loads(line)
                        out[str(r["name"])] = str(r.get("text") or "")
            self._informal[vol] = out
        return self._informal[vol]

    def lean_anchor(self, ref: str) -> str:
        """The text of the companion between `-- anchor: name` and `-- end: name`. ref is path#name."""
        path, _, name = ref.partition("#")
        if not name:
            raise KeyError(f"{ref}: give the anchor after #")
        if not self.lean_root:
            raise KeyError(f"{ref}: give the companion with --lean")
        p = os.path.join(self.lean_root, path)
        if not os.path.exists(p):
            raise KeyError(f"{ref}: the file {path} is not in the companion")
        text = read(p)
        m = re.search(r"^[ \t]*-- anchor: " + re.escape(name) + r"[ \t]*\n(.*?)^[ \t]*-- end: " + re.escape(name)
                      + r"[ \t]*$", text, re.S | re.M)
        if not m:
            raise KeyError(f"{ref}: the file has no anchor {name}")
        return m.group(1).rstrip("\n")
