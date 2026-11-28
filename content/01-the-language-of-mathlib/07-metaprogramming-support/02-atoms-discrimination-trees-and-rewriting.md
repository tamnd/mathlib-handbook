---
title: Atoms, discrimination trees and rewriting
kind: api
modules:
  - Mathlib.Util.AtomM
  - Mathlib.Util.AtomM.Recurse
  - Mathlib.Lean.Meta.RefinedDiscrTree
  - Mathlib.Lean.Meta.RefinedDiscrTree.Basic
  - Mathlib.Lean.Meta.RefinedDiscrTree.Encode
  - Mathlib.Lean.Meta.RefinedDiscrTree.Initialize
  - Mathlib.Lean.Meta.RefinedDiscrTree.Lookup
  - Mathlib.Lean.Meta.DiscrTree
  - Mathlib.Lean.Meta.KAbstractPositions
  - Mathlib.Lean.Meta.Tactic.Rewrite
  - Mathlib.Lean.Meta.CongrTheorems
  - Mathlib.Lean.Meta.Simp
  - Mathlib.Util.Simp
  - Mathlib.Util.DischargerAsTactic
  - Mathlib.Util.AtLocation
  - Mathlib.Util.SynthesizeUsing
  - Mathlib.Util.ElabWithoutMVars
  - Mathlib.Util.TermReduce
explains:
  E2: [Lean.Meta.FastSubsingleton.elim, Mathlib.Tactic.AtomM.addAtom]
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

## Atoms, discrimination trees and rewriting

### Overview

A user of Mathlib meets the modules of this section through tactics, not through their names. The tactic `ring` proves $(a + b)^2 = a^2 + 2ab + b^2$ because it treats $a$ and $b$ as indeterminates of a polynomial ring. The tactic `abel` does the same for commutative groups. Both tactics must first decide which subterms of the goal are the indeterminates, and when two subterms are the same indeterminate. The monad `Mathlib.Tactic.AtomM` does this bookkeeping. The tactic `rw??` and the point and click suggestions search the whole library for a lemma that rewrites a selected subterm. They use a data structure, the refined discrimination tree `Lean.Meta.RefinedDiscrTree`, that finds the candidate lemmas fast. The tactic `fun_prop` also stores its lemmas in this tree.

The other modules hold smaller tools that tactics share: the positions of a pattern in a term (for `rw` and `nth_rw`), congruence lemmas (for `congr!`), helper functions for the simplifier, and functions that run a rewriting procedure at a hypothesis or at the goal. The section requires no knowledge of metaprogramming. It explains what each tool computes, in the language of terms and substitutions, and it explains the effects that a user sees: why `ring` fails on a goal that `ring!` proves, why a search tool ranks one lemma above another, and why `rw` sometimes reports that the motive is not type correct.

### The library around it

**Atoms.** Let $R$ be a commutative ring and $e_1, e_2$ two expressions of type $R$ built from $+$, $\cdot$, $-$, numerals and powers with numeral exponents. Every other subterm, such as $\sin x$ or $f(y)$, is an *atom*. Replace the atoms by indeterminates $x_1, \dots, x_n$. Then $e_1$ and $e_2$ become polynomials $p_1, p_2 \in \mathbb{Z}[x_1, \dots, x_n]$, and $e_1 = e_2$ holds for all values of the atoms if $p_1 = p_2$. The tactic `ring` computes a normal form of $p_1$ and of $p_2$ and compares them. The correctness of this method depends on one point: two occurrences of the same atom must get the same indeterminate.

The module `Mathlib.Util.AtomM` provides the monad `Mathlib.Tactic.AtomM` for this. Its state `Mathlib.Tactic.AtomM.State` holds an array `Mathlib.Tactic.AtomM.State.atoms` of the atoms seen so far, and the index of an atom in this array is the index $i$ of its indeterminate $x_i$. Its context `Mathlib.Tactic.AtomM.Context` holds a transparency setting `Mathlib.Tactic.AtomM.Context.red` and a function `Mathlib.Tactic.AtomM.Context.evalAtom` that simplifies an atom before it is stored. The function `Mathlib.Tactic.AtomM.addAtom` takes a term $t$. It compares $t$ with each stored atom by definitional equality at the given transparency. If it finds a stored atom $s$ with $t \equiv s$, it returns the index of $s$ and the term $s$. Otherwise it appends $t$ and returns the new index. The variant `Mathlib.Tactic.AtomM.containsThenAdd` also returns whether the atom was already present, and `Mathlib.Tactic.AtomM.addAtomQ` and `Mathlib.Tactic.AtomM.containsThenAddQ` are the forms for typed quotations. The function `Mathlib.Tactic.AtomM.run` runs a computation from an empty list of atoms. The comparison uses `Mathlib.Tactic.isDefEqSafe`, a form of definitional equality that returns false instead of an error.

**Proposition (atoms are well defined).** Let $t_1, \dots, t_m$ be the terms given to `Mathlib.Tactic.AtomM.addAtom` in order, and let $\iota(k)$ be the index returned for $t_k$. If $\iota(k) = \iota(l)$, then $t_k$ and $t_l$ are definitionally equal at the given transparency.

*Proof sketch.* The index $\iota(k)$ is the position of a stored atom $s$, and either $t_k$ is $s$ or the comparison $t_k \equiv s$ succeeded. The same holds for $t_l$ with the same $s$. Definitional equality is symmetric and transitive, so $t_k \equiv t_l$. $\square$

The converse fails: two atoms that are equal as real numbers but not definitionally equal get different indices. This explains the transparency setting. The tactic `ring` compares atoms at reducible transparency, so it does not unfold a definition to identify two atoms. The tactic `ring!` compares them at default transparency. It can prove more goals, and it is slower. The comparison runs against every stored atom, so the cost grows with the square of the number of atoms.

The module `Mathlib.Util.AtomM.Recurse` runs a normalization inside the atoms. For example, the goal $\sin(x + y) + \sin(y + x) = 2 \sin(x + y)$ has the atoms $\sin(x + y)$ and $\sin(y + x)$, which are different. The tactic `ring_nf` first normalizes the arguments of the atoms, so that both become $\sin(x + y)$, and then normalizes the sum. The function `Mathlib.Tactic.AtomM.recurse` does this bottom to top. The function `Mathlib.Tactic.AtomM.onSubexpressions` applies a normalization to the subterms of a term, and `Mathlib.Tactic.AtomM.RecurseM.run` runs a whole computation in the monad `Mathlib.Tactic.AtomM.RecurseM`. The configuration `Mathlib.Tactic.AtomM.Recurse.Config` has three fields: `Mathlib.Tactic.AtomM.Recurse.Config.red` for the transparency, `Mathlib.Tactic.AtomM.Recurse.Config.zetaDelta` to unfold local definitions, and `Mathlib.Tactic.AtomM.Recurse.Config.contextual` to use the hypotheses of an implication. The tactics `ring_nf`, `abel_nf` and `field_simp` use this module. Other tactics, such as `linear_combination`, `module`, `order` and `itauto`, use `Mathlib.Tactic.AtomM` directly.

**Discrimination trees.** A search tool has a term $e$ and a library of many thousands of lemmas. It must find the lemmas whose pattern, such as the left side $a + b$ of `add_comm`, matches $e$ or a subterm of $e$. A test of each lemma by unification is too slow. A *discrimination tree* is a trie indexed by the preorder traversal of the patterns. Each node of a term gives a key: a constant with its number of arguments, a variable, a literal, a sort, a binder. A metavariable of the pattern gives a *star*, which matches any subterm. To look up $e$, the tree reads the keys of $e$ and follows the matching edges and the star edges. Only the lemmas at the leaves that it reaches are tested by unification.

Lean core has a plain discrimination tree. The module `Mathlib.Lean.Meta.DiscrTree` adds two functions to it: `Lean.Meta.DiscrTree.getSubexpressionMatches` finds the entries that match $e$ or a subterm of $e$, and `Lean.Meta.DiscrTree.keysSpecific` tests whether a key sequence is more specific than a single star or an equation between stars.

The refined discrimination tree of `Mathlib.Lean.Meta.RefinedDiscrTree.Basic` has more key kinds. The type `Lean.Meta.RefinedDiscrTree.Key` has the constructors `Lean.Meta.RefinedDiscrTree.Key.const`, `Lean.Meta.RefinedDiscrTree.Key.fvar`, `Lean.Meta.RefinedDiscrTree.Key.bvar`, `Lean.Meta.RefinedDiscrTree.Key.lit`, `Lean.Meta.RefinedDiscrTree.Key.sort`, `Lean.Meta.RefinedDiscrTree.Key.lam`, `Lean.Meta.RefinedDiscrTree.Key.forall`, `Lean.Meta.RefinedDiscrTree.Key.proj`, `Lean.Meta.RefinedDiscrTree.Key.opaque`, `Lean.Meta.RefinedDiscrTree.Key.star` and `Lean.Meta.RefinedDiscrTree.Key.labelledStar`. The keys for $\lambda$, $\forall$ and bound variables let the tree look inside binders. So a lemma about $\sum_{i \in \mathrm{range}\, n} i$ is indexed by the body $i$ of the sum, and not only by the constant `Finset.sum`. The labelled stars record which metavariable each star comes from. The pattern $?a + ?a$ of a lemma has two stars with the same label, and the tree matches it with $x + y$ only when $x$ and $y$ have the same keys.

The lookup gives each match a *score*: the number of keys that had to agree. The docstring of the module gives an example. The pattern of `add_comm` is $\texttt{HAdd.hAdd}\ {*_0}\ {*_0}\ {*_0}\ {*_1}\ {*_2}\ {*_3}$. Matched with $(1 + 2) + 3$, the head constant gives one point, and the second and third occurrence of the star $*_0$ give one point together, so the score is 2. A lemma with a more specific pattern, such as `add_assoc`, gets a higher score. The structure `Lean.Meta.RefinedDiscrTree.MatchResult` stores the results by score, and `Lean.Meta.RefinedDiscrTree.MatchResult.flatten` lists them from the highest score down. This order is the order in which `rw??` shows its suggestions.

A pattern of the form $\lambda x, f(?m\ x)$ can reduce to $f$ by $\eta$-reduction when $?m$ is the identity. The tree stores such a pattern under both key sequences. So the lemma about the continuity of $\lambda y, \exp(f(y))$ is found for the goal `Continuous Real.exp`. The module `Mathlib.Lean.Meta.RefinedDiscrTree.Encode` computes these keys: `Lean.Meta.RefinedDiscrTree.encodeExpr` gives the canonical key sequence, and `Lean.Meta.RefinedDiscrTree.encodeExprWithEta` gives all of them.

The tree is *lazy*. To build it from all imported lemmas takes time, so the keys of a lemma are computed only when a lookup reaches its node. A node stores the pending entries of type `Lean.Meta.RefinedDiscrTree.LazyEntry`, and `Lean.Meta.RefinedDiscrTree.evalLazyEntry` computes the next key of an entry. The module `Mathlib.Lean.Meta.RefinedDiscrTree.Initialize` builds trees: `Lean.Meta.RefinedDiscrTree.insert` adds one entry, `Lean.Meta.RefinedDiscrTree.createImportedDiscrTree` adds all imported constants in parallel, and `Lean.Meta.RefinedDiscrTree.createModuleDiscrTree` adds the constants of the current file. The function `Lean.Meta.RefinedDiscrTree.blacklistInsertion` excludes automatically generated declarations. The module `Mathlib.Lean.Meta.RefinedDiscrTree.Lookup` holds the lookup `Lean.Meta.RefinedDiscrTree.getMatch`, and the module `Mathlib.Lean.Meta.RefinedDiscrTree` holds the entry points `Lean.Meta.RefinedDiscrTree.findImportMatches`, `Lean.Meta.RefinedDiscrTree.findModuleMatches` and `Lean.Meta.RefinedDiscrTree.findMatches`. The tactics `exact?` and `simp` do not use this tree: they use the discrimination trees of Lean core.

**Positions and rewriting.** The tactic `rw [h]` with $h : a = b$ abstracts every occurrence of $a$ in the goal $P$. It forms the motive $\lambda x, P[x/a]$ and uses $h$ to pass from $P$ to $P[b/a]$. The module `Mathlib.Lean.Meta.KAbstractPositions` works with the positions of these occurrences. The function `Lean.Meta.kabstractPositions` lists the positions where a pattern occurs. The function `Lean.Meta.viewKAbstractSubExpr` takes a position and returns the subterm there with the occurrence number that `nth_rw` needs to reach it. The function `Lean.Meta.kabstractIsTypeCorrect` tests whether the motive is type correct. The motive can fail to be type correct when another part of the goal depends on $a$, for example a proof $h' : a \neq 0$ inside the goal. This is the reason for the error "motive is not type correct". The module `Mathlib.Lean.Meta.Tactic.Rewrite` holds `Lean.Expr.rewrite` and `Lean.Expr.rewriteType`, which rewrite a proof term or its type with an equation.

**Congruence.** The module `Mathlib.Lean.Meta.CongrTheorems` makes the congruence lemmas of the tactic `congr!`. For a function $f$ of $n$ arguments, a congruence lemma states $a_1 = a_1' \to \dots \to a_n = a_n' \to f(a_1, \dots, a_n) = f(a_1', \dots, a_n')$. When the type of $a_2$ depends on $a_1$, the equation $a_2 = a_2'$ is between different types, and the lemma uses heterogeneous equality. The function `Lean.Meta.mkRichHCongr` makes a lemma in which each hypothesis can use the equations before it. The function `Lean.Meta.mkHCongrWithArity'` is a simpler form. The class `Lean.Meta.FastSubsingleton` is a copy of the class of subsingletons with few instances, so that a search for it fails fast. Its instances cover propositions (`Lean.Meta.instFastSubsingleton`), decidability instances (`Lean.Meta.instFastSubsingletonDecidable`), empty types through `Lean.Meta.FastIsEmpty`, and function types into subsingletons. The function `Lean.Meta.fastSubsingletonElim` closes a goal $a = b$ in such a type. This is why `congr!` does not create goals for two proofs of the same proposition or for two decidability instances.

**Proposition.** If $\alpha$ is a `Lean.Meta.FastSubsingleton`, then $a = b$ for all $a, b : \alpha$.

*Proof.* The class has one field: an instance of `Subsingleton`. A subsingleton has at most one element by definition, so $a = b$. This is `Lean.Meta.FastSubsingleton.elim`, and `Lean.Meta.FastSubsingleton.helim` is the form for heterogeneous equality. $\square$

**Simplifier helpers.** The module `Mathlib.Lean.Meta.Simp` lets a tactic call the simplifier with a list of lemma names. The function `Lean.Meta.simpOnlyNames` simplifies a term as `simp only [...]` does, `Lean.Meta.simpTheoremsOfNames` builds the set of lemmas, and `Lean.Meta.Simp.Context.ofNames` builds a simplifier context. The functions `Lean.Meta.simpType` and `Lean.Meta.simpEq` apply a simplification to a type or to both sides of an equation. The functions `Lean.Meta.getAllSimpDecls`, `Lean.Meta.getAllSimpAttrs` and `Lean.Meta.isInSimpSet` answer questions about simp sets, such as whether a lemma has a given simp attribute. The module `Mathlib.Util.Simp` adds `Lean.Meta.Simp.Methods.dischargeQ?`, a typed call of the discharger. The module `Mathlib.Util.DischargerAsTactic` adds `wrapSimpDischarger`, which turns a discharger into a tactic, so that a user can write `simp (discharger := ...)` with it.

**Rewriting at a location.** Many tactics have the form: from a term $e$, compute $e'$ and a proof of $e = e'$. The module `Mathlib.Util.AtLocation` turns such a procedure into a tactic that acts on the goal, on a hypothesis, or on every location given by `at h₁ h₂ ⊢` or `at *`. The functions are `Mathlib.Tactic.transformAtTarget`, `Mathlib.Tactic.transformAtLocalDecl`, `Mathlib.Tactic.transformAtLocation` and `Mathlib.Tactic.transformAtNondepPropLocation`. The type `Mathlib.Tactic.BehaviorIfUnchanged` decides what happens when the procedure changes nothing: `Mathlib.Tactic.BehaviorIfUnchanged.silent`, `Mathlib.Tactic.BehaviorIfUnchanged.warning` or `Mathlib.Tactic.BehaviorIfUnchanged.error`. The tactics `ring_nf`, `push`, `pull` and `field_simp` are built in this way. So `ring_nf at h ⊢` and `push_neg at *` share their handling of locations.

**Small tools.** The module `Mathlib.Util.SynthesizeUsing` holds `synthesizeUsing`, which makes a term of a given type with a tactic and returns the open goals, and `synthesizeUsing'`, which requires the tactic to close all goals. The tactics `linarith`, `field_simp` and `cancel_denoms` use them to prove side conditions. The module `Mathlib.Util.ElabWithoutMVars` holds `elabTermWithoutNewMVars`, which elaborates a term given to a tactic and fails if the term has holes. The module `Mathlib.Util.TermReduce` defines four term elaborators: `beta% t` reduces the applications of $\lambda$-terms at the head of $t$, `delta% t` unfolds the head constant of $t$, `zeta% t` replaces local definitions by their values, and `reduceProj% t` reduces each projection of a structure constructor, such as $(x, y).1$ to $x$. Their syntax kinds are `Mathlib.Util.TermReduce.betaStx`, `Mathlib.Util.TermReduce.deltaStx`, `Mathlib.Util.TermReduce.zetaStx` and `Mathlib.Util.TermReduce.reduceProjStx`. The command `irreducible_def` uses `delta%` in the lemma that it generates.

#### Common errors

1. A user expects `ring` to identify the atoms $f(a + b)$ and $f(b + a)$. It does not: they are not definitionally equal. Use `ring_nf`, which normalizes inside the atoms, or rewrite with `add_comm` first.
2. A user expects `ring` to unfold a local definition to see that two atoms agree. It compares atoms at reducible transparency. Use `ring!`, or unfold the definition first.
3. A user reads the order of the suggestions of `rw??` as an order of usefulness. The order is the score of the match, the number of keys that agree, together with a few rules on the number of new goals and the length of names.

### Exercises

1. (A) List the atoms that `ring` sees in the goal $x \cdot \sin y + \sin y \cdot x = 2 x \sin y$, and the polynomials in $\mathbb{Z}[x_1, x_2]$ that it compares.
2. (A) Write the preorder key sequence of the pattern $?a \cdot (?b + ?c)$ of `mul_add`, with labelled stars, in the style of the pattern of `add_comm` given above.
3. (B) Compute the score of the match of the pattern of `add_assoc`, $(?a + ?b) + ?c$, with the term $(1 + 2) + 3$, and explain why it is higher than the score of `add_comm`.
4. (B) Give a goal in which `rw [h]` with $h : n = m$ fails because the motive is not type correct. Use a term whose type depends on $n$, such as an element of `Fin n`.
5. (B) Prove that the list of atoms of `Mathlib.Tactic.AtomM` never holds two atoms that are definitionally equal at the given transparency.
6. (C) The comparison of a new atom with the stored atoms costs one test of definitional equality for each stored atom. Give a bound on the number of tests for a goal with $n$ distinct atoms and $m$ occurrences of atoms, and explain how a canonical form of the atoms, with a hash table, reduces it.

### Reference

<?reference?>
