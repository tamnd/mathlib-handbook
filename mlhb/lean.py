"""Lean in print (spec 12.5).

The companion writes the highlighted Lean of each of its files as SubVerso JSON:

    lake build MathlibHandbook.V13.C05.Examples:highlighted
    # .lake/build/highlighted/MathlibHandbook/V13/C05/Examples.json

The folder of these files is the option --highlight of mlhb. The JSON has a table of code nodes and a table of
tokens. The items of the file, in order, give back the whole text of the file. Each token has a kind: keyword,
const, var, a comment, a number, a string, sorry and some others. A const token has the name of the constant and
its signature.

A Lean block goes to the book as raw LaTeX and raw HTML. The LaTeX is a Verbatim environment of fvextra with the
macros of tex/lean.sty, so the PDF needs no shell escape and no Pygments. The HTML is a <pre class="lean"> with
one <span> for each token. A constant of Mathlib is a link to its declaration page, and its signature is the
title of the link.

A signature of <?decl?> comes from the type of the index. A small lexer gives it the same classes: a name of the
index is a constant, and the words of Lean such as fun and Type are keywords.
"""

from __future__ import annotations

import html
import json
import os
import re
from dataclasses import dataclass

from .map import decl_url


@dataclass
class Token:
    kind: str           # keyword, const, var, comment, doc, num, str, sorry, text
    text: str
    name: str = ""      # the constant of a const token
    sig: str = ""       # the signature of a const token


# The kinds of SubVerso and the class of the book. A kind that is not here prints as plain text.
_KINDS = {"keyword": "keyword", "const": "const", "var": "var", "lineComment": "comment", "blockComment": "comment",
          "commentDelim": "comment", "docComment": "doc", "num": "num", "str": "str", "sorry": "sorry",
          "moduleName": "const", "levelConst": "keyword", "levelVar": "var", "levelOp": "text", "operator": "text",
          "bracket": "text", "delim": "text", "anonCtor": "text", "unknown": "text", "withType": "text",
          "option": "keyword", "docString": "doc"}


def _name(parts) -> str:
    if isinstance(parts, list):
        return ".".join(str(p) for p in parts)
    return str(parts or "")


class Highlighted:
    """The token stream of one file of the companion."""

    def __init__(self, data: dict):
        self.d = data["data"]
        self.tokens: list[Token] = []
        for it in data.get("items") or []:
            self._walk(it["code"])

    def _tok(self, n: int) -> Token:
        t = self.d["tokens"][str(n)]
        kind = t.get("kind")
        if isinstance(kind, dict):
            k, info = next(iter(kind.items()))
            info = info or {}
        else:
            k, info = str(kind), {}
        cls = _KINDS.get(k, "text")
        if k == "keyword" and t["content"] == "sorry":
            cls = "sorry"
        if cls == "const":
            sig = " ".join(str(info.get("signature") or "").split())
            return Token(cls, t["content"], _name(info.get("name")), sig)
        return Token(cls, t["content"])

    def _walk(self, n: int):
        stack = [n]
        while stack:
            node = self.d["code"][str(stack.pop())]
            k, v = next(iter(node.items()))
            if k == "token":
                self.tokens.append(self._tok(v["tok"]))
            elif k == "text":
                self.tokens.append(Token("text", v["str"]))
            elif k == "seq":
                stack.extend(reversed(v["highlights"]))
            elif k in ("tactics", "span", "point"):
                if "content" in v:
                    stack.append(v["content"])
            # other nodes (goals and messages alone) have no text of the file

    @property
    def text(self) -> str:
        return "".join(t.text for t in self.tokens)

    def lines(self) -> list[list[Token]]:
        """The tokens of each line. A token with a newline in it is cut at the newline."""
        out: list[list[Token]] = [[]]
        for t in self.tokens:
            parts = t.text.split("\n")
            for i, p in enumerate(parts):
                if i:
                    out.append([])
                if p:
                    out[-1].append(Token(t.kind, p, t.name, t.sig))
        return out

    def anchor(self, name: str) -> list[list[Token]]:
        """The lines between `-- anchor: name` and `-- end: name`."""
        lines = self.lines()
        text = ["".join(t.text for t in ln).strip() for ln in lines]
        try:
            a = text.index(f"-- anchor: {name}")
            b = text.index(f"-- end: {name}", a + 1)
        except ValueError:
            raise KeyError(f"the highlighted file has no anchor {name}") from None
        body = lines[a + 1:b]
        while body and not body[-1]:
            body.pop()
        return body


class Store:
    """The folder of the highlighted files: --highlight."""

    def __init__(self, root: str):
        self.root = root
        self._files: dict[str, Highlighted] = {}

    def file(self, path: str) -> Highlighted:
        """The highlighted file of a Lean path of the companion: MathlibHandbook/V13/C05/Examples.lean."""
        if path not in self._files:
            p = os.path.join(self.root, re.sub(r"\.lean$", "", path) + ".json")
            if not os.path.exists(p):
                raise KeyError(f"{path} has no highlighted file in {self.root}")
            with open(p, encoding="utf-8") as f:
                self._files[path] = Highlighted(json.load(f))
        return self._files[path]

    def anchor(self, ref: str) -> list[list[Token]]:
        path, _, name = ref.partition("#")
        return self.file(path).anchor(name)


# The words of Lean that a pretty-printed type can have.
_WORDS = {"fun", "Type", "Sort", "Prop", "let", "have", "show", "from", "by", "if", "then", "else", "match", "with",
          "do", "return", "∀", "∃", "λ", "Π", "Σ"}
_LEX = re.compile(r"(\s+)|([A-Za-z_\u0370-\u03ff\u1d00-\u1dbf\u2100-\u214f\U0001d400-\U0001d7ff][\w.'!?\u2080-\u209c"
                  r"\u0370-\u03ff\u1d00-\u1dbf\u2100-\u214f\U0001d400-\U0001d7ff]*)|([0-9]+)|(.)", re.S)


def lex_signature(kind: str, name: str, typ: str, names) -> list[list[Token]]:
    """The tokens of `kind name : type`. A name of the index is a constant."""
    toks = [Token("keyword", kind), Token("text", " "), Token("const", name, name, typ), Token("text", " : ")]
    for m in _LEX.finditer(typ):
        ws, word, num, other = m.groups()
        if ws:
            toks.append(Token("text", ws))
        elif word:
            if word in _WORDS:
                toks.append(Token("keyword", word))
            elif word in names:
                toks.append(Token("const", word, word))
            else:
                toks.append(Token("text", word))
        elif num:
            toks.append(Token("num", num))
        else:
            toks.append(Token("keyword" if other in _WORDS else "text", other))
    return [toks]


# LaTeX: the special characters of a Verbatim with commandchars=\\\{\}
_TEX = {"\\": r"\LeanBS{}", "{": r"\LeanOB{}", "}": r"\LeanCB{}"}
_TEX_CMD = {"keyword": "LeanKw", "const": "LeanConst", "var": "LeanVar", "comment": "LeanComment",
            "doc": "LeanComment", "num": "LeanNum", "str": "LeanStr", "sorry": "LeanSorry"}


def _tex(s: str) -> str:
    return "".join(_TEX.get(c, c) for c in s)


def latex(lines: list[list[Token]]) -> str:
    out = []
    for ln in lines:
        bits = []
        for t in ln:
            cmd = _TEX_CMD.get(t.kind)
            bits.append(f"\\{cmd}{{{_tex(t.text)}}}" if cmd else _tex(t.text))
        out.append("".join(bits))
    return "\\begin{LeanCode}\n" + "\n".join(out) + "\n\\end{LeanCode}"


def is_mathlib(name: str, names) -> bool:
    """A constant that has a declaration page: a name of the index, or with no index, not of the companion."""
    if names is not None:
        return name in names
    return bool(name) and not name.startswith("MathlibHandbook.")


def html_block(lines: list[list[Token]], names=None) -> str:
    out = []
    for ln in lines:
        bits = []
        for t in ln:
            s = html.escape(t.text, quote=False)
            if t.kind == "text":
                bits.append(s)
                continue
            title = f' title="{html.escape(t.sig)}"' if t.sig else ""
            if t.kind == "const" and is_mathlib(t.name, names):
                bits.append(f'<a class="lean-const" href="{decl_url(t.name)}"{title}>{s}</a>')
            else:
                bits.append(f'<span class="lean-{t.kind}"{title}>{s}</span>')
        out.append("".join(bits))
    return '<pre class="lean"><code>' + "\n".join(out) + "</code></pre>"


def block(lines: list[list[Token]], names=None) -> str:
    """The Markdown of a Lean block: a raw LaTeX block and a raw HTML block. Pandoc keeps the one of the format."""
    return "```{=latex}\n" + latex(lines) + "\n```\n\n```{=html}\n" + html_block(lines, names) + "\n```"
