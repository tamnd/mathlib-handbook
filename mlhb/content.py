"""The content of the handbook: content/<NN-slug>/<NN-chapter>/ with an intro.md, one file NN-<slug>.md per
section and an optional problems.md (spec 12.1).

The id of a volume is V00 to V34, and its folder is 00-<slug> to 34-<slug>. The id of a chapter is C01, C02 and so
on, from the NN of its folder. The id of a section is V13.C05.S02, from the NN of its file. A volume folder has a
volume.yaml with number, title, subtitle, level and the prefixes that it covers. A section file has the YAML front
matter of spec 07.7, and its text starts with a ## heading.
"""

from __future__ import annotations

import glob
import os
import re
from dataclasses import dataclass, field

import yaml

# spec 07.8: the order is the order of the work, and `stale` is the lowest, since it needs work again
STATUSES = ("stale", "planned", "drafted", "checked", "reviewed")
LEVELS = ("guide", "foundation", "undergraduate", "undergraduate to graduate", "graduate", "graduate to research",
          "research", "catalogue")
KINDS = ("theory", "api", "instance", "tactic", "survey", "guide")
DEPTHS = ("E3", "E2", "E1")


def read(path: str) -> str:
    with open(path, encoding="utf-8") as f:
        return f.read()


def front(text: str) -> tuple[dict, str]:
    """Split a Markdown file into its YAML front matter and its body."""
    if text.startswith("---\n"):
        end = text.find("\n---\n", 4)
        if end > 0:
            return yaml.safe_load(text[4:end]) or {}, text[end + 5:]
    return {}, text


_SLUG = re.compile(r"[^a-z0-9 -]")


def anchor(heading: str) -> str:
    """The anchor of a heading: lower case, spaces become hyphens, other punctuation goes."""
    s = _SLUG.sub("", heading.strip().lower())
    return re.sub(r" +", "-", s).strip("-")


def as_list(x) -> list[str]:
    if x is None or x == "":
        return []
    if isinstance(x, (list, tuple)):
        return [str(i) for i in x]
    return [str(x)]


@dataclass
class Section:
    path: str
    fm: dict
    body: str
    id: str = ""            # V13.C05.S02
    volume_level: str = ""

    @property
    def status(self) -> str:
        return str(self.fm.get("status") or "drafted")

    @property
    def title(self) -> str:
        return str(self.fm.get("title") or "")

    @property
    def kind(self) -> str:
        return str(self.fm.get("kind") or "")

    @property
    def modules(self) -> list[str]:
        return as_list(self.fm.get("modules"))

    @property
    def explains(self) -> dict[str, list[str]]:
        """The declarations of each depth. E1 can be the word auto (spec 07.7); it gives an empty list here."""
        ex = self.fm.get("explains") or {}
        if not isinstance(ex, dict):
            return {}
        return {d: as_list(v) for d, v in ex.items() if v != "auto"}

    @property
    def e1_auto(self) -> bool:
        ex = self.fm.get("explains") or {}
        return isinstance(ex, dict) and ex.get("E1") == "auto"

    @property
    def families(self) -> list[str]:
        return as_list(self.fm.get("families"))

    @property
    def reads_with(self) -> list[str]:
        return as_list(self.fm.get("reads_with"))

    @property
    def requires(self) -> list[str]:
        return as_list(self.fm.get("requires"))

    @property
    def lean(self) -> list[str]:
        return as_list(self.fm.get("lean"))


@dataclass
class Chapter:
    num: int          # the NN of the folder
    slug: str
    dir: str
    title: str
    intro: str        # intro.md without its # title line
    sections: list[Section] = field(default_factory=list)
    problems: str = ""   # problems.md, if any

    @property
    def id(self) -> str:
        return f"C{self.num:02d}"

    @property
    def status(self) -> str:
        """The lowest status of its sections (spec 07.8). A chapter with no sections is planned."""
        if not self.sections:
            return "planned"
        rank = min(STATUSES.index(s.status) if s.status in STATUSES else 0 for s in self.sections)
        return STATUSES[rank]

    @property
    def draft(self) -> bool:
        return self.status != "reviewed"

    @property
    def text(self) -> str:
        return "\n\n".join(s.body.strip("\n") for s in self.sections)


@dataclass
class Volume:
    num: int          # 0 to 34
    dirname: str      # 13-general-topology
    dir: str
    title: str
    subtitle: str
    intro: str
    meta: dict = field(default_factory=dict)   # volume.yaml
    chapters: list[Chapter] = field(default_factory=list)

    @property
    def draft(self) -> bool:
        """A volume with a chapter that is not reviewed fails the release rule of spec 12.6. It is built as a draft."""
        return not self.chapters or any(c.draft for c in self.chapters)

    @property
    def reviewed(self) -> int:
        return sum(1 for c in self.chapters if not c.draft)

    @property
    def id(self) -> str:
        """V00 to V34."""
        return f"V{self.num:02d}"

    @property
    def label(self) -> str:
        """The number of the volume as the book prints it: 0 to 34."""
        return str(self.num)

    @property
    def number(self) -> str:
        return self.label

    @property
    def index(self) -> int:
        return self.num

    @property
    def item_prefix(self) -> str:
        """The start of the number of an item: Theorem 13.5.2 is item 2 of chapter 5 of Volume 13."""
        return self.label + "."

    @property
    def slug(self) -> str:
        return self.dirname.split("-", 1)[1] if "-" in self.dirname else self.dirname

    @property
    def level(self) -> str:
        return str(self.meta.get("level") or "")

    @property
    def prefixes(self) -> list[str]:
        return as_list(self.meta.get("prefixes"))

    @property
    def squares(self) -> list[float]:
        """The cover: one square per chapter, filled by its status."""
        fill = {"planned": 0.0, "stale": 0.1, "drafted": 0.25, "checked": 0.6, "reviewed": 1.0}
        return [fill.get(c.status, 0.0) for c in self.chapters]


def _intro(path: str) -> tuple[str, str]:
    """The title (its # line) and the rest of an intro.md."""
    if not os.path.exists(path):
        return "", ""
    _, body = front(read(path))
    lines = body.lstrip("\n").split("\n")
    if lines and lines[0].startswith("# "):
        return lines[0][2:].strip(), "\n".join(lines[1:]).strip("\n")
    return "", body.strip("\n")


_VDIR = re.compile(r"^([0-9][0-9])-")


def load_volume(d: str) -> Volume:
    vy = os.path.join(d, "volume.yaml")
    v = (yaml.safe_load(read(vy)) or {}) if os.path.exists(vy) else {}
    base = os.path.basename(d)
    num = int(base[:2])
    _, vintro = _intro(os.path.join(d, "intro.md"))
    slug = base.split("-", 1)[1] if "-" in base else base
    vol = Volume(num, base, d, str(v.get("title") or slug.replace("-", " ").capitalize()),
                 str(v.get("subtitle") or ""), vintro, v)
    for cdir in sorted(glob.glob(os.path.join(d, "[0-9][0-9]-*"))):
        if not os.path.isdir(cdir):
            continue
        cbase = os.path.basename(cdir)
        cnum = int(cbase[:2])
        title, intro = _intro(os.path.join(cdir, "intro.md"))
        secs = []
        for sp in sorted(glob.glob(os.path.join(cdir, "[0-9][0-9]-*.md"))):
            fm, body = front(read(sp))
            sid = f"{vol.id}.C{cnum:02d}.S{int(os.path.basename(sp)[:2]):02d}"
            secs.append(Section(sp, fm, body, sid, vol.level))
        pp = os.path.join(cdir, "problems.md")
        problems = front(read(pp))[1].strip("\n") if os.path.exists(pp) else ""
        if not secs and not intro and not title:   # a chapter of the plan with nothing written yet
            continue
        if not title:
            title = cbase[3:].replace("-", " ").capitalize()
        vol.chapters.append(Chapter(cnum, cbase[3:], cdir, title, intro, secs, problems))
    return vol


def load(content: str) -> list[Volume]:
    out = []
    for d in sorted(glob.glob(os.path.join(content, "*"))):
        if os.path.isdir(d) and _VDIR.match(os.path.basename(d)):
            out.append(load_volume(d))
    return sorted(out, key=lambda v: v.num)
