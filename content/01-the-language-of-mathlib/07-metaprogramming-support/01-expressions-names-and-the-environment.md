---
title: Expressions, names and the environment
kind: api
modules:
  - Mathlib.Lean.Expr.Basic
  - Mathlib.Lean.Expr.ExtraRecognizers
  - Mathlib.Lean.Expr.Rat
  - Mathlib.Lean.Quote
  - Mathlib.Util.Qq
  - Mathlib.Lean.Name
  - Mathlib.Lean.Environment
  - Mathlib.Lean.EnvExtension
  - Mathlib.Lean.FoldEnvironment
  - Mathlib.Lean.CoreM
  - Mathlib.Lean.Meta
  - Mathlib.Lean.Meta.Basic
  - Mathlib.Lean.LocalContext
  - Mathlib.Util.Tactic
  - Mathlib.Lean.Elab.Tactic.Basic
  - Mathlib.Lean.Elab.Tactic.Meta
  - Mathlib.Lean.Exception
  - Mathlib.Lean.ContextInfo
  - Mathlib.Lean.Elab.InfoTree
  - Mathlib.Lean.GoalsLocation
  - Mathlib.Lean.MessageData.ForExprs
  - Mathlib.Lean.MessageData.Trace
  - Mathlib.Lean.Json
  - Mathlib.Lean.Thunk
  - Mathlib.Util.Export
  - Mathlib.Util.GetAllModules
explains:
  E2: ["Lean.Expr.rat?", Thunk.add_get, Thunk.prod_get_fst]
  E1: auto
families: []
requires: [V01.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Expressions, names and the environment

### Overview

A tactic of Mathlib is a program that reads the goal and builds a proof term. The goal and the proof are *expressions*: trees whose nodes are constants, variables, applications, $\lambda$-abstractions, $\forall$-types, literals and sorts. The theorem $a + b = b + a$ is the expression $\texttt{Eq}\ (\texttt{HAdd.hAdd}\ a\ b)\ (\texttt{HAdd.hAdd}\ b\ a)$ with the implicit type and instance arguments added. Lean core defines expressions, names and the *environment*, the table of all declarations. The modules of this section add small functions on these objects that the tactics of Mathlib share.

A mathematician does not call these functions in a proof. A reader meets them in two ways: in the source of a tactic that the reader wants to understand, and in the error messages of tactics, which these functions produce. This section explains the main families: recognizers that read a term, constructors that build one, functions on names and on the environment, functions on goals, and the tools that read the information that Lean records about a file. The next section uses these tools for atoms, search and rewriting.

### The library around it

**Recognizers.** A *recognizer* reads the shape of an expression. It returns the parts if the shape matches, and nothing otherwise. The module `Mathlib.Lean.Expr.Basic` has recognizers for relations: `Lean.Expr.le?` and `Lean.Expr.lt?` return the type and the two sides of $a \leq b$ and $a < b$, `Lean.Expr.ne?'` reads both $a \neq b$ and $\neg (a = b)$, and `Lean.Expr.sides?` reads an equation, an equivalence of propositions or a heterogeneous equation. The recognizer `Lean.Expr.numeral?` returns $n$ when the expression is a numeral $n$, written as a literal, as `OfNat.ofNat n`, or as a tower of successors of zero. The recognizer `Lean.Expr.zero?` tests for $0$, and `Lean.Expr.type?` returns the universe level of a sort. The recognizer `Lean.Expr.isSorryAx` detects the axiom behind `sorry`. The module `Mathlib.Lean.Expr.ExtraRecognizers` adds `Lean.Expr.coeTypeSet?`, which detects a set $s$ used as a type, either as `Set.Elem` of $s$ or as the subtype $\{x \mid x \in s\}$.

The module `Mathlib.Lean.Expr.Rat` recognizes numbers in normal form, which are the numbers that `norm_num` produces. A natural number in normal form is a numeral `OfNat.ofNat n` with a literal $n$, in any type. An integer in normal form is $n$ or $-n$ for a natural number $n$ in normal form. A rational in normal form is an integer in normal form, or $n / d$ where $n$ is an integer in normal form, $d$ is a natural number in normal form, $d \neq 1$, and $\gcd(n, d) = 1$. The test `Lean.Expr.isExplicitNumber` checks this, and `Lean.Expr.rat?` returns the rational number.

**Proposition (uniqueness of the normal form).** Each rational number $q$ has exactly one normal form that `Lean.Expr.rat?` accepts.

*Proof.* If $q \in \mathbb{Z}$, then $q = n / d$ with $\gcd(n, d) = 1$ and $d > 0$ forces $d = 1$, which the definition excludes, so the only form is the integer $q$. If $q \notin \mathbb{Z}$, then $q = n / d$ with $d \geq 2$. Two such forms $n / d = n' / d'$ give $n d' = n' d$. Since $\gcd(n, d) = 1$, $d$ divides $d'$, and by symmetry $d'$ divides $d$. So $d = d'$ and $n = n'$. $\square$

**Constructors.** The functions `Lean.Expr.ofNat` and `Lean.Expr.ofInt` build the numeral of a natural number or an integer in a given type, with a search for the instance. The function `Lean.mkConst'` builds a constant with fresh universe levels. The function `Lean.Expr.mkProjection` builds the projection $e.\mathrm{field}$, also for a field of a parent structure, and `Lean.Expr.reduceProjStruct?` reduces a projection of a constructor, such as $(x, y).1$ to $x$. The functions `Lean.Expr.modifyArg`, `Lean.Expr.setArg` and `Lean.Expr.getArg?` change or read one argument of an application. The function `Lean.Expr.eraseProofs` replaces every proof inside an expression by `sorry`, which shows whether the data part of a definition depends on a proof.

The module `Mathlib.Util.Qq` adds functions for typed quotations. A typed quotation is an expression together with its type, checked when the tactic is compiled, so that a tactic cannot build an ill typed term by mistake. The functions `Qq.mkNatLitQ`, `Qq.mkIntLitQ`, `Qq.mkIntNumeralQ` and `Qq.mkRatNumeralQ` build numerals, `Qq.mkFinLitQ` builds an element of `Fin n`, `Qq.mkListLitQ` and `Qq.mkSetLiteralQ` build list and set literals, and `Qq.mkDecideProofQ` builds a proof by `decide`. The theorem `Qq.QuotedDefEq.rfl` states that a quoted term is definitionally equal to itself. The module `Mathlib.Lean.Quote` gives the instances `Mathlib.instQuoteInt` and `Mathlib.instQuoteRat`, which turn a computed number into a numeral, for example in a "Try this" suggestion. The numeral has no type ascription, so it takes the expected type. The syntax $-7 / 2$ denotes $-3.5$ in a field of characteristic zero, but $-4$ in $\mathbb{Z}$, where $/$ is integer division.

**Names and the environment.** A name is a list of components, such as `Nat.Prime.two_le`. The module `Mathlib.Lean.Name` has `Lean.Name.splitAt`, `Lean.Name.fromComponents`, `Lean.Name.mapPrefix`, `Lean.Name.isPrefixOf?`, `Lean.Name.updateLast`, `Lean.Name.lastComponentAsString` and `Lean.Name.decapitalize`. The test `Lean.Name.willRoundTrip` checks that a name prints in a form that Lean parses back to the same name. The functions `allNames` and `allNamesByModule` list the declarations of the environment that satisfy a predicate, and `Lean.Name.isBlackListed` excludes internal and automatically generated names. The module `Mathlib.Lean.Environment` has `Lean.Environment.findTheoremConstVal?` and `Lean.Environment.findConstValOfKind?`, which find a declaration of a given kind. The module `Mathlib.Lean.FoldEnvironment` has `Lean.Meta.foldImportedDecls`, which visits all imported declarations in parallel tasks, and `Lean.Meta.foldCurrFileDecls` for the current file. The module `Mathlib.Lean.CoreM` has `CoreM.withImportModules`, which runs a computation in an environment that imports given modules: a script uses it to read Mathlib. The module `Mathlib.Lean.EnvExtension` has one instance, `instInhabitedState_mathlib`, for the state of scoped environment extensions, which store the data of attributes such as `simp`.

**Goals.** A goal is a metavariable with a type and a local context. The module `Mathlib.Lean.Meta` has `Lean.MVarId.existsi`, the step of `refine ⟨e₁, e₂, ?_⟩`, `Lean.MVarId.intros!`, which introduces hypotheses and unfolds $\neg p$ to $p \to \mathrm{False}$ on the way, and `Lean.MVarId.let`, which adds a local definition. The module `Mathlib.Lean.Meta.Basic` has checks such as `Lean.Meta.ensureHasType`, `Lean.Meta.ensureIsSort` and `Lean.Meta.ensureIsFunction`, and `Lean.Meta.mkRel`, which builds the relation $a \mathrel{R} b$ for a relation given by name. The module `Mathlib.Lean.LocalContext` has `Lean.LocalContext.firstDeclM` and `Lean.LocalContext.lastDeclM`, which find the first or last hypothesis with a property. The module `Mathlib.Util.Tactic` changes a goal in place: `Mathlib.Tactic.modifyTarget` changes its type, and `Mathlib.Tactic.modifyLocalDecl` and `Mathlib.Tactic.modifyLocalContext` change its hypotheses. These functions do not check that the new type is definitionally equal to the old one, so a tactic must use them with care. The modules `Mathlib.Lean.Elab.Tactic.Basic` and `Mathlib.Lean.Elab.Tactic.Meta` add `Lean.Elab.Tactic.getMainTarget''`, `Lean.Elab.Tactic.commitIfNoExPreservingInfoAndMessages` and `Lean.Elab.runTactic'`, which run a tactic and keep its hover information and messages. The module `Mathlib.Lean.Exception` has `successIfFail`, which succeeds when a computation fails, and `Lean.Exception.isFailedToSynthesize`, which recognizes the error of a failed instance search.

**The information of a file.** When Lean checks a file, it records an *info tree*: for each piece of syntax, the goals, the terms and the local context at that point. The editor reads it to show the goal under the cursor. The module `Mathlib.Lean.Elab.InfoTree` searches this tree: `Lean.Elab.InfoTree.getDeclBodyInfos` lists the bodies of the declarations in it, with their context, and `Lean.Elab.collectTryThisSuggestions` collects the "Try this" suggestions of tactics such as `exact?`. The module `Mathlib.Lean.ContextInfo` runs a computation at a node of the tree, with `Lean.Elab.ContextInfo.runMetaMWithMessages`, `Lean.Elab.ContextInfo.runTactic` and related functions. Linters use them to run a tactic again at the place where the user wrote it. The module `Mathlib.Lean.GoalsLocation` reads a location that the user selects in the goal view, with `Lean.SubExpr.GoalsLocation.rootExpr`, `Lean.SubExpr.GoalsLocation.pos` and `Lean.SubExpr.GoalsLocation.fvarId?`. The tactic `rw??` uses it. The module `Mathlib.Lean.MessageData.ForExprs` reads the expressions inside a message, with `Lean.MessageData.getExprs` and `Lean.MessageData.firstExpr?`, and the module `Mathlib.Lean.MessageData.Trace` has `Lean.MessageData.dedupByString` and `Lean.MessageData.extractInstName` for trace messages, such as the trace of an instance search.

**Data formats.** The module `Mathlib.Lean.Json` gives JSON encodings of the unit type, of `Fin n` and of subtypes, for example `Lean.instToJsonFin_mathlib` and `Lean.instFromJsonSubtypeOfDecidablePred_mathlib`. The decoder of a subtype checks the predicate, and the decoder of `Fin n` checks the bound. The module `Mathlib.Util.Export` writes the declarations of the environment in a plain text format for an independent proof checker. It is deprecated, and its docstrings point to the external tool lean4export, so new code must not use it. The module `Mathlib.Util.GetAllModules` has `getAllFiles` and `getAllModulesSorted`, which list the files of a library for the scripts of the project.

**Thunks.** A *thunk* of type `Thunk α` is a value of type $\alpha$ that is computed only when it is needed, and at most once. The module `Mathlib.Lean.Thunk` gives the product `Thunk.prod` and the sum `Thunk.add`, with the instance `Thunk.instAdd_mathlib`, and the decidable equality `Thunk.instDecidableEq_mathlib`, which compares the values. The simp lemmas state the values: `Thunk.get_pure`, `Thunk.get_mk`, `Thunk.prod_get_fst`, `Thunk.prod_get_snd` and `Thunk.add_get`. For example, `Thunk.add_get` states that the value of $a + b$ is the sum of the values of $a$ and of $b$. The proof is `rfl`: the sum is defined as the thunk that computes this sum. The same holds for `Thunk.prod_get_fst`.

#### Common errors

1. A tactic author tests `Lean.Expr.numeral?` on a term that `norm_num` printed as $3 / 4$ and gets nothing. A fraction is not a natural numeral. Use `Lean.Expr.rat?`.
2. A user reads `-7 / 2` in a "Try this" suggestion as a rational number in every type. The numeral takes the expected type, and in $\mathbb{Z}$ it denotes $-4$.
3. A tactic author changes a goal with `Mathlib.Tactic.modifyTarget` to a type that is not definitionally equal. The kernel then rejects the final proof term, and the error appears far from its cause.

### Exercises

1. (A) Write the expression tree of $a \cdot b \leq c$ for real numbers, with the implicit arguments, and give the output of `Lean.Expr.le?` on it.
2. (A) Decide which of $6/4$, $-3/1$, $-3$, $5/7$ and $0/2$ are rationals in normal form in the sense of `Lean.Expr.isExplicitNumber`.
3. (B) Give the normal form of the rational number $-42/28$ and prove that it is the only one.
4. (B) Explain why `Lean.Expr.ne?'` must read both $a \neq b$ and $\neg (a = b)$, using the definition of $\neq$ in Lean.
5. (B) Prove `Thunk.prod_get_snd` and explain why the proof is `rfl`.
6. (C) The function `Lean.Expr.eraseProofs` replaces proofs by `sorry`. Explain why the result has the same type as the input, using proof irrelevance.

### Reference

<?reference?>
