---
title: Notation, printing and commands
kind: api
modules:
  - Mathlib.Util.Notation3
  - Mathlib.Lean.Elab.Term
  - Mathlib.Util.Superscript
  - Mathlib.Util.Delaborators
  - Mathlib.Util.PPOptions
  - Mathlib.Util.DelabNonCanonical
  - Mathlib.Lean.PrettyPrinter.Delaborator
  - Mathlib.Util.FormatTable
  - Mathlib.Util.CountHeartbeats
  - Mathlib.Util.SleepHeartbeats
  - Mathlib.Util.PrintSorries
  - Mathlib.Util.AssertNoSorry
  - Mathlib.Util.LongNames
  - Mathlib.Util.TransImports
  - Mathlib.Util.WhatsNew
  - Mathlib.Util.ParseCommand
  - Mathlib.Util.CompileInductive
  - Mathlib.Util.AddRelatedDecl
  - Mathlib.Util.AliasIn
  - Mathlib.Util.WithWeakNamespace
  - Mathlib.Util.CodeActions
  - Mathlib.Util.CodeActions.BinderPlicity
  - Mathlib.Util.VersoRoles
  - Mathlib.Lean.Linter
explains:
  E2: [Mathlib.Notation3.notation3, formatTable, Mathlib.Tactic.addRelatedDecl, Mathlib.PrintSorries.collectSorries]
  E1: auto
families: []
requires: [V01.C04, V01.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Notation, printing and commands

### Overview

Mathematical notation in Mathlib comes from two directions. A *parser* reads the text $\forall^\mathrm{f}\, x \text{ in } f,\ p(x)$ and builds the term `Filter.Eventually (fun x => p x) f`. A *delaborator* reads the term in a goal and prints it back as notation. A good notation needs both: without the delaborator, the goal view shows the raw term, and the user does not recognize the statement. The command `notation3` of `Mathlib.Util.Notation3` makes both from one line. Most binder notations of Mathlib, such as $\bigsqcup_i f(i)$, $\bigcup_i s_i$, $\forall^\mathrm{f}$ and $\exists^\mathrm{f}$, are declared with it.

The other modules of this section are of three kinds. Some control printing: the superscript parser behind $\mathbb{R}^n$-style notation, the printing of $\forall \varepsilon > 0$ and of $\Pi$-types, and the printing of instances that are not the canonical ones. Some are commands for a user who inspects a file: they count the work of a proof, find the uses of `sorry`, or list the new declarations of a command. The rest are support for authors of attributes and of documentation. Read this section after the chapter on the naming convention, since several of these tools make new names.

### The library around it

**The command notation3.** A declaration with `notation3` has a list of items and a right side. An item is a string, a variable, the binder item `(...)`, or a fold. Mathlib declares the eventually quantifier of filters by

`notation3 "∀ᶠ "(...)" in "f", "r:(scoped p => Filter.Eventually p f) => r`

The item `(...)` accepts any binders of the extended form: $x$, $x\ y$, $x : \alpha$, or $x > 0$. The item `r:(scoped p => ...)` says that the body $r$ is turned into a function $p = \lambda x, r$ of the binders. So $\forall^\mathrm{f}\, x \text{ in } f,\ x > 0$ means `Filter.Eventually (fun x => x > 0) f`. With several binders, the function is applied once for each binder. The syntax kind of the command is `Mathlib.Notation3.notation3`, and its items have the syntax kinds `Mathlib.Notation3.bindersItem`, `Mathlib.Notation3.identOptScoped` and `Mathlib.Notation3.foldAction`. A fold item, with the keyword `foldl` or `foldr` (`Mathlib.Notation3.foldKind`), declares a list notation: the docstring example makes `MyList[a, b, c]` into nested applications of a constructor. The term elaborators `expand_binders%`, `expand_foldl%` and `expand_foldr%` do the expansion.

The command also makes a delaborator. It elaborates the right side as a pattern, with `Lean.Elab.Term.elabPattern` of the module `Mathlib.Lean.Elab.Term`, and turns the pattern into a *matcher*, a function of type `Mathlib.Notation3.Matcher`. A matcher reads a term, checks that it has the shape of the pattern, and records the subterms for each variable in a `Mathlib.Notation3.MatchState`. The matchers are built from `Mathlib.Notation3.matchVar`, `Mathlib.Notation3.matchApp`, `Mathlib.Notation3.matchLambda`, `Mathlib.Notation3.matchForall`, `Mathlib.Notation3.matchScoped` and `Mathlib.Notation3.matchFoldl`, and `Mathlib.Notation3.mkExprMatcher` makes one from a term. The option `(prettyPrint := false)` (`Mathlib.Notation3.prettyPrintOpt`) turns the delaborator off. A `local notation3` can mention the variables of a `variable` command, which the plain `notation` command cannot.

**Superscripts and subscripts.** The module `Mathlib.Util.Superscript` defines the parsers `Mathlib.Tactic.superscript` and `Mathlib.Tactic.subscript`, with the term forms `Mathlib.Tactic.superscriptTerm` and `Mathlib.Tactic.subscriptTerm`. A superscript is the longest sequence of superscript characters, so `2⁶⁴` reads as $2$ with the superscript $64$, and a local macro can expand it to `2 ^ 64`. The tables `Mathlib.Tactic.Superscript.Mapping.superscript` and `Mathlib.Tactic.Superscript.Mapping.subscript` map each special character to its normal form. Unicode has few such characters: the digits, some letters and a few signs. So a superscript can hold only a short expression. Mathlib uses the parser for the notation `!₂[x, y]` of vectors in the Euclidean space `EuclideanSpace ℝ (Fin 2)`, for the notation of the simplices of the simplex category, and for local notations such as $\mathbb{R}^n$ and $\mathbb{S}^n$ in the statement of the Poincaré conjecture. The delaborators `Mathlib.Tactic.delabSuperscript` and `Mathlib.Tactic.delabSubscript` succeed only when the printed term has a superscript form.

**Printing quantifiers and products.** Lean writes the statement $\forall \varepsilon, \varepsilon > 0 \to P(\varepsilon)$ with an implication. The module `Mathlib.Util.Delaborators` prints it as `∀ ε > 0, P ε`. The delaborator `PiNotation.delabPi` recognizes the binder predicates $> z$, $< z$, $\geq z$, $\leq z$, $\in s$, $\notin s$, $\subseteq s$, $\subset s$, $\supseteq s$ and $\supset s$. The delaborator `exists_delab` does the same for $\exists x > 0, P(x)$, and `delabNotIn` prints $\neg (a \in s)$ as $a \notin s$. The option `pp.mathlib.binderPredicates`, declared in `Mathlib.Util.PPOptions` as `Mathlib.pp.mathlib.binderPredicates` and read by `Mathlib.getPPBinderPredicates`, turns this off. The module also defines the notation `Π x : α, β x` for the dependent function type $\prod_{x : \alpha} \beta(x)$, which is the type `(x : α) → β x`. The command `open scoped PiNotation` makes every dependent function type that is not a proposition print in this form.

**Non-canonical instances.** A type can carry two structures of the same kind, for example two topologies on one set. The statement `IsOpen s` then uses the instance that Lean finds, and a statement about the other topology must give it explicitly. The module `Mathlib.Util.DelabNonCanonical` helps to print such statements. The test `Lean.Meta.isCanonicalInstance` checks whether an instance is definitionally equal to the one that instance search finds. The delaborators `Delab.Noncanonical.delabUnary` and `Delab.Noncanonical.delabBinary` print a special notation only when an instance is not canonical. In the topology library, this prints `IsOpen[t] s` for a set that is open for a topology $t$ that is not the instance, and the plain `IsOpen s` otherwise. The module `Mathlib.Lean.PrettyPrinter.Delaborator` has helpers for delaborators: `Lean.PrettyPrinter.Delaborator.annotateGoToDef` makes go to definition on printed notation jump to a given declaration.

**Commands for inspecting a file.** These commands write an information message. A user can try them in any file that imports Mathlib.

| Command | What it reports |
| --- | --- |
| `#count_heartbeats in cmd` | the heartbeats, the unit of work of Lean, used by `cmd` |
| `#count_heartbeats! n in cmd` | the minimum, the maximum and the spread over $n$ runs of `cmd` |
| `guard_min_heartbeats n in cmd` | an error if `cmd` uses fewer than $n$ heartbeats |
| `#print sorries` | the declarations with `sorry` that a declaration depends on |
| `assert_no_sorry foo` | an error if `foo` depends on `sorry` |
| `#whats_new in cmd` | the declarations that `cmd` adds to the environment |
| `#trans_imports` | the number of modules that the current file imports, directly or not |
| `#long_names` and `#long_instances` | the declarations with a very long name |
| `#parse p => "text"` | the result or the error of a parser on a string |

A proof that is slow often uses many heartbeats. The default limit is set by the option `maxHeartbeats`, and `#count_heartbeats in` also suggests a value of this option when a declaration needs more. The functions behind the commands are `Mathlib.CountHeartbeats.elabForHeartbeats` and `Mathlib.CountHeartbeats.runTacForHeartbeats` for heartbeats, `Mathlib.PrintSorries.collectSorries` for `sorry`, `Mathlib.WhatsNew.whatsNew` for the new declarations, and `Mathlib.GuardExceptions.parseCmd` for parsing. The tactic `sleep_heartbeats n` and the function `sleepAtLeastHeartbeats` use up $n$ heartbeats without effect, for tests. The function `formatTable` of `Mathlib.Util.FormatTable` prints a table of strings with columns aligned by `Alignment`, and `String.justify` pads one string.

**Support for attributes.** Several attributes of Mathlib make a new declaration from an old one: `simps` makes the simp lemmas of a structure, `reassoc` makes the form of a lemma about composition with an extra morphism, and `elementwise` makes the form that applies a morphism to an element. The function `Mathlib.Tactic.addRelatedDecl` of `Mathlib.Util.AddRelatedDecl` does the common work: it adds the new declaration with its universe variables and docstring, and it applies the attributes given by the argument `(attr := ...)`, whose syntax kind is `Mathlib.Tactic.optAttrArg`. So `@[reassoc (attr := simp)]` marks both lemmas as simp lemmas. The attribute `alias_in` of `Mathlib.Util.AliasIn` (`aliasIn`) adds an alias of a declaration in another namespace. The command `with_weak_namespace` of `Mathlib.Util.WithWeakNamespace` (`Lean.Elab.Command.withWeakNamespace`) changes the current namespace and keeps the scoped notations open. The notation `scoped[NS]` uses it.

The command `compile_inductive% T` of `Mathlib.Util.CompileInductive` gives code for the recursor of an inductive type $T$, so that a definition by the recursor can be evaluated with `#eval`. The code generator of Lean does not support recursors directly. The command `compile_def%` does the same for a definition without code. The functions are `Mathlib.Util.compileInductive` and `Mathlib.Util.compileDefn`.

**Support for the editor and the documentation.** The module `Mathlib.Util.CodeActions` imports the code actions of Mathlib and has no declarations of its own. Its submodule `Mathlib.Util.CodeActions.BinderPlicity` gives the code action `Mathlib.CodeAction.binderPlicity`: in the editor, it switches a binder `(x : α)` to `{x : α}` and back. The module `Mathlib.Util.VersoRoles` defines roles for docstrings in the Verso format: `url` makes a link, `library_note` refers to a library note and checks that it exists, and `cite` refers to an entry of the bibliography of Mathlib, a `Mathlib.VersoRoles.Citation`. The module `Mathlib.Lean.Linter` has `Lean.Linter.whenLinterOption`, `Lean.Linter.whenNotLinterOption` and `Lean.Linter.whenLinterActivated`, which run code only when a linter option is on or off. A user turns a linter off with `set_option linter.<name> false`.

#### Common errors

1. A user declares a binder notation with `notation` and sees the raw term `Filter.Eventually (fun x => ...) f` in the goal. The plain command makes no delaborator for a notation with binders. Use `notation3` with a `scoped` item.
2. A user writes a superscript with characters that have no superscript form, such as `xᵃ⁺ᵇ⁽ᶜ⁾`, and expects a parse of any term. Only the characters of the table parse. Use the power `x ^ (a + b)`.
3. A user turns off `pp.mathlib.binderPredicates` to see the implication in `∀ ε > 0, P ε`, and is surprised that other notations still print. The option controls only the binder predicates. Use `set_option pp.notation false` to print every term without notation.

### Exercises

1. (A) Write the term that $\forall^\mathrm{f}\, x \text{ in } f,\ \forall^\mathrm{f}\, y \text{ in } g,\ p(x, y)$ denotes, with `Filter.Eventually` and $\lambda$-terms.
2. (A) Write the statement $\forall \varepsilon > 0, \exists \delta > 0, \forall x, |x| < \delta \to |f(x)| < \varepsilon$ as Lean prints it with `pp.mathlib.binderPredicates` off.
3. (A) The type $\Pi x : \alpha, \beta(x)$ with a constant family $\beta(x) = \gamma$ is a familiar type. Name it, and give its form in Lean.
4. (B) Give a type with two topologies, and explain why the statement that a set is open for the second topology needs the notation `IsOpen[t] s`.
5. (B) A declaration with `notation3` for the indexed supremum $\bigsqcup_i f(i)$ uses `scoped f => iSup f`. Explain what term `⨆ i j, f i j` denotes.
6. (C) A local notation for the power is made with the superscript parser and the macro that turns `a` with superscript `b` into `a ^ b`. Explain why `2⁶⁴` and `2 ^ 64` give the same term, and why a superscript such as `xⁿ⁺¹` gives $x^{n+1}$ and not $x^n + 1$.

### Reference

<?reference?>
