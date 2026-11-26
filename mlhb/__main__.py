"""mlhb: build The Mathlib Handbook from content/, the map of tamnd/mathlib and the companion tamnd/mathlib-lean.

    python -m mlhb check    [--volume ID,...|all]
    python -m mlhb number   [--write]
    python -m mlhb resolve  [--volume ID,...|all]
    python -m mlhb build    [--volume ID,...|all] [--formats html,tex,pdf,epub] [--out build]
    python -m mlhb new volume V13
    python -m mlhb new section V13/C05 compact-metric

A volume is named by its id or its number: V13 or 13. Each command takes --map PATH (default ../mathlib, or the
environment variable MLHB_MAP), --lean PATH (default ../mathlib-lean, or MLHB_LEAN), --index PATH (or
MLHB_INDEX; no default), --highlight PATH (the SubVerso JSON files of the companion, or MLHB_HIGHLIGHT; no
default) and --content PATH (default content/).
"""

from __future__ import annotations

import argparse
import datetime
import json
import os
import shutil
import sys

import yaml

from .book import Book, out_name
from .content import anchor
from .paths import ROOT


def edition() -> dict:
    """The file EDITION (12.6): one key and one value on each line."""
    out = {"version": "0.0.0", "mathlib-tag": "", "mathlib": "", "mathlib-lean": "", "mathlib-commit": ""}
    p = os.path.join(ROOT, "EDITION")
    if os.path.exists(p):
        with open(p, encoding="utf-8") as f:
            for line in f:
                k, _, v = line.strip().partition(" ")
                if k:
                    out[k] = v.strip()
    return out


def load(args) -> Book:
    book = Book(os.path.abspath(args.content), os.path.abspath(args.map), args.index,
                os.path.abspath(args.lean) if args.lean else "", edition().get("mathlib", ""), args.highlight)
    m = book.map
    idx = "no index" if m.decls is None else f"{len(m.decls)} declarations"
    if m.highlight is None:
        idx += ", no highlighted files (the Lean blocks of <?lean?> are plain text)"
    print(f"map {m.root}: {len(m.volumes)} volumes, {len(m.plans)} plans, {len(m.books)} books, {idx}; "
          f"{len(book.volumes)} volumes in content", file=sys.stderr)
    return book


def pick(book: Book, which: str):
    if which == "all":
        return list(book.volumes)
    out, missing = [], []
    for x in (t.strip() for t in which.split(",") if t.strip()):
        try:
            v = book.volume(x)
        except KeyError:
            missing.append(x)
            continue
        if v not in out:
            out.append(v)
    if missing:
        raise SystemExit(f"no volume {', '.join(missing)} in {book.content}")
    return out


def cmd_check(args):
    from .check import check
    book = load(args)
    faults, warns = check(pick(book, args.volume), book.map, os.path.dirname(book.content), book.volumes)
    for w in warns:
        print(f"warning: {w}")
    for f in faults:
        print(f)
    print(f"{len(faults)} faults, {len(warns)} warnings", file=sys.stderr)
    return 1 if faults else 0


def cmd_number(args):
    from . import number
    book = load(args)
    number.run(book.volumes, args.write)
    return 0


def cmd_resolve(args):
    """Resolve the directives of each section and print the faults. It writes nothing."""
    from .resolve import ResolveError, resolve
    book = load(args)
    bad = 0
    for v in pick(book, args.volume):
        for ch in v.chapters:
            for s in ch.sections:
                try:
                    resolve(book.map, v, s, s.body)
                except ResolveError as e:
                    print(e)
                    bad += 1
    print(f"{bad} sections with a directive that does not resolve", file=sys.stderr)
    return 1 if bad else 0


def cmd_build(args):
    from . import epub, html, latex
    from .resolve import ResolveError
    book = load(args)
    ed = edition()
    version = ed["version"]
    date = args.date or datetime.date.today().isoformat()
    fmts = set(args.formats.split(","))
    os.makedirs(args.out, exist_ok=True)
    report = {}
    for v in pick(book, args.volume):
        try:
            md, st = book.markdown(v)
        except ResolveError as e:
            print(f"volume {v.id}: {e}", file=sys.stderr)
            report[v.id] = {"ok": False, "error": str(e)}
            continue
        d = os.path.join(args.out, v.dirname)
        os.makedirs(d, exist_ok=True)
        info = dict(st)
        if fmts & {"tex", "pdf"}:
            info.update(latex.build(book, v, md, d, version, date, pdf="pdf" in fmts))
        if "epub" in fmts:
            info.update(epub.build(book, v, md, d, version, date))
        if "html" in fmts:
            info.update(html.build(book, v, md, os.path.join(args.out, "html", v.dirname), version, date))
        name = out_name(v, version, ed.get("mathlib-tag", ""))
        for ext in ("pdf", "epub"):
            src = os.path.join(d, f"main.{ext}")
            if ext in fmts and os.path.exists(src):
                dst = os.path.join(args.out, f"{name}.{ext}")
                shutil.copy(src, dst)
                info[ext] = dst
        err = info.pop("error", None)
        report[v.id] = info
        print(f"volume {v.id} {v.title}: " + json.dumps({k: x for k, x in info.items() if k != "lean"}),
              file=sys.stderr)
        if err:
            print(err, file=sys.stderr)
    if "html" in fmts:
        html.index(book, os.path.join(args.out, "html"), version, date)
    with open(os.path.join(args.out, "report.json"), "w", encoding="utf-8") as f:
        json.dump(report, f, indent=1)
    bad = [n for n, i in report.items()
           if i.get("ok") is False or i.get("epub_ok") is False or i.get("html_ok") is False]
    return 1 if bad else 0


def _volume_dir(book: Book, vid: str) -> str:
    for v in book.volumes:
        if v.id == vid:
            return v.dir
    mv = book.map.volumes.get(vid)
    if mv is None:
        raise SystemExit(f"{vid} is not a volume of blueprint/volumes.yaml")
    return os.path.join(book.content, f"{vid[1:]}-{anchor(str(mv['title']).split(':')[-1])}")


def cmd_new(args):
    book = load(args)
    if args.what == "volume":
        vid = args.target.upper()
        d = _volume_dir(book, vid)
        vy = os.path.join(d, "volume.yaml")
        if os.path.exists(vy):
            raise SystemExit(f"{vy} exists")
        mv = book.map.volumes[vid]
        os.makedirs(d, exist_ok=True)
        meta = {"number": int(vid[1:]), "title": mv["title"], "subtitle": "", "level": mv.get("level", ""),
                "prefixes": mv.get("prefixes") or []}
        with open(vy, "w", encoding="utf-8") as f:
            yaml.safe_dump(meta, f, sort_keys=False, allow_unicode=True)
        print(f"wrote {os.path.relpath(vy, ROOT)}")
        return 0
    vid, _, cid = args.target.upper().partition("/")
    plan = book.map.plans.get(vid)
    if not plan:
        raise SystemExit(f"no plan blueprint/sections/{vid}.yaml")
    ch = next((c for c in plan.get("chapters") or [] if c.get("id") == cid), None)
    if ch is None:
        raise SystemExit(f"the plan of {vid} has no chapter {cid}")
    secs = ch.get("sections") or []
    sec = next((s for s in secs if anchor(str(s.get("title") or "")) == args.slug), None)
    if sec is None:
        raise SystemExit(f"the chapter {vid}.{cid} has no section with the slug {args.slug}: "
                         + ", ".join(anchor(str(s.get('title') or '')) for s in secs))
    cdir = os.path.join(_volume_dir(book, vid), f"{cid[1:]}-{anchor(str(ch.get('title') or cid))[:40].strip('-')}")
    os.makedirs(cdir, exist_ok=True)
    path = os.path.join(cdir, f"{str(sec['id'])[-2:]}-{args.slug}.md")
    if os.path.exists(path):
        raise SystemExit(f"{path} exists")
    explains = {k: list(sec[k]) for k in ("E3", "E2") if sec.get(k)}
    explains["E1"] = "auto"
    fm = {"title": sec.get("title"), "kind": sec.get("kind") or "theory", "modules": sec.get("modules") or [],
          "explains": explains, "families": sec.get("families") or [], "requires": sec.get("requires") or [],
          "reads_with": [], "lean": [], "mathlib": str(plan.get("mathlib") or ""), "status": "planned",
          "drafted_by": "", "reviewed_by": []}
    with open(path, "w", encoding="utf-8") as f:
        f.write("---\n" + yaml.safe_dump(fm, sort_keys=False, allow_unicode=True) + "---\n\n## "
                + str(sec.get("title")) + "\n")
    print(f"wrote {os.path.relpath(path, ROOT)}")
    return 0


def main(argv=None):
    common = argparse.ArgumentParser(add_help=False)
    common.add_argument("--map", default=argparse.SUPPRESS,
                        help="the checkout of tamnd/mathlib (default ../mathlib or $MLHB_MAP)")
    common.add_argument("--lean", default=argparse.SUPPRESS,
                        help="the checkout of tamnd/mathlib-lean (default ../mathlib-lean or $MLHB_LEAN)")
    common.add_argument("--index", default=argparse.SUPPRESS,
                        help="index.jsonl.gz or the folder that has it (default $MLHB_INDEX)")
    common.add_argument("--highlight", default=argparse.SUPPRESS,
                        help="the folder of the SubVerso JSON files of the companion (default $MLHB_HIGHLIGHT)")
    common.add_argument("--content", default=argparse.SUPPRESS, help="the content folder (default content/)")
    ap = argparse.ArgumentParser(prog="mlhb", parents=[common])
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("check", parents=[common])
    c.add_argument("--volume", default="all")
    nb = sub.add_parser("number", parents=[common])
    nb.add_argument("--write", action="store_true")
    r = sub.add_parser("resolve", parents=[common])
    r.add_argument("--volume", default="all")
    b = sub.add_parser("build", parents=[common])
    b.add_argument("--volume", default="all")
    b.add_argument("--formats", default="html,pdf,epub")
    b.add_argument("--out", default=os.path.join(ROOT, "build"))
    b.add_argument("--date", default="")
    n = sub.add_parser("new", parents=[common])
    n.add_argument("what", choices=["volume", "section"])
    n.add_argument("target", help="V13 for a volume, V13/C05 for a section")
    n.add_argument("slug", nargs="?", default="", help="the slug of the section title in the plan")
    args = ap.parse_args(argv)
    if not hasattr(args, "map"):
        args.map = os.environ.get("MLHB_MAP") or os.path.join(ROOT, "..", "mathlib")
    if not hasattr(args, "lean"):
        args.lean = os.environ.get("MLHB_LEAN") or os.path.join(ROOT, "..", "mathlib-lean")
    if not hasattr(args, "index"):
        args.index = os.environ.get("MLHB_INDEX", "")
    if not hasattr(args, "highlight"):
        args.highlight = os.environ.get("MLHB_HIGHLIGHT", "")
    if not hasattr(args, "content"):
        args.content = os.path.join(ROOT, "content")
    if args.cmd == "new" and args.what == "section" and not args.slug:
        ap.error("new section needs a slug")
    return {"check": cmd_check, "build": cmd_build, "number": cmd_number, "resolve": cmd_resolve,
            "new": cmd_new}[args.cmd](args)


if __name__ == "__main__":
    sys.exit(main() or 0)
