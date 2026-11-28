---
title: The limit superior and the limit inferior
kind: api
modules:
  - Mathlib.Order.LiminfLimsup
explains:
  E2: [Filter.limsup_eq, Filter.limsup_eq_iInf_iSup, Filter.limsup_eq_iInf_iSup_of_nat, Filter.liminf_le_limsup, Filter.mem_limsup_iff_frequently_mem, Filter.cofinite.limsup_set_eq, Filter.limsup_compl, Filter.frequently_lt_of_lt_limsup]
  E1: auto
families: []
requires: [V04.C03, V04.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The limit superior and the limit inferior

### Overview

For a sequence $(u_n)$ of real numbers, the limit superior is $\limsup_n u_n = \inf_n \sup_{k \ge n} u_k$. It is the largest value that the sequence approaches infinitely often. The limit inferior is the dual notion. The two numbers exist for each bounded sequence, they satisfy $\liminf \le \limsup$, and they are equal exactly when the sequence converges. For a sequence of sets $(A_n)$, the limit superior is the set of the points that lie in infinitely many $A_n$. This is the set of the Borel and Cantelli lemma in probability.

Mathlib defines both notions once, for a function $u : \beta \to \alpha$ with values in a conditionally complete lattice and for an arbitrary filter $f$ on $\beta$. The sequence case is the filter `Filter.atTop` on `ℕ`. The set case is the complete lattice `Set α`. The definition uses the order filters of Chapter 3, the infimum and the supremum of Chapter 4, and the conditionally complete lattices of the first section of this chapter.

The module `Mathlib.Order.LiminfLimsup` holds the definitions, the formulas as an infimum of suprema, the comparison lemmas and the rules for the lattice operations. The boundedness predicates that the lemmas need are in `Mathlib.Order.Filter.IsBounded`, and the topological facts, such as the equality of the two limits for a convergent sequence, are in the topology volumes.

### The library around it

#### The definitions

Let $f$ be a filter on $\alpha$, with $\alpha$ a conditionally complete lattice. The definition `Filter.limsSup` gives
$$\operatorname{limsSup} f = \inf \{ a \mid x \le a \text{ eventually for } f \}.$$
The set on the right holds the eventual upper bounds of $f$. For a function $u : \beta \to \alpha$ and a filter $f$ on $\beta$, `Filter.limsup u f` is `limsSup (map u f)`. So `Filter.limsup_eq` gives the form that a proof uses most:
$$\limsup_f u = \inf \{ a \mid u(x) \le a \text{ eventually for } f \}.$$
`Filter.liminf` and `Filter.limsInf` are the duals, with the supremum of the eventual lower bounds, and `Filter.liminf_eq` is the dual of `Filter.limsup_eq`. The argument order is the function first and then the filter: `limsup u atTop`.

A third form restricts the points to a predicate $p$. `Filter.blimsup u f p` is the infimum of the $a$ with $p(x) \Rightarrow u(x) \le a$ eventually. The lemma `Filter.blimsup_eq_limsup` turns it into a limit superior along the filter $f \sqcap \mathcal{P}(\{x \mid p(x)\})$. The bounded forms come up for sets of the form "the points that lie in infinitely many $A_n$ with $n$ prime".

#### Formulas in a complete lattice

In a complete lattice each set has an infimum and a supremum, and the definitions become explicit formulas.

| Lean name | Statement |
|---|---|
| `Filter.limsup_eq_iInf_iSup` | $\limsup_f u = \inf_{s \in f} \sup_{x \in s} u(x)$ |
| `Filter.liminf_eq_iSup_iInf` | $\liminf_f u = \sup_{s \in f} \inf_{x \in s} u(x)$ |
| `Filter.limsup_eq_iInf_iSup_of_nat` | $\limsup_{n} u_n = \inf_n \sup_{i \ge n} u_i$ |
| `Filter.limsup_eq_iInf_iSup_of_nat'` | $\limsup_{n} u_n = \inf_n \sup_i u_{i+n}$ |
| `Filter.liminf_eq_iSup_iInf_of_nat` | $\liminf_{n} u_n = \sup_n \inf_{i \ge n} u_i$ |
| `Filter.HasBasis.limsup_eq_iInf_iSup` | the same formula with the sets of a basis of $f$ |
| `Filter.limsup_top_eq_iSup` | $\limsup_{\top} u = \sup_i u(i)$ |
| `Filter.limsup_bot` | $\limsup_{\bot} u = \bot$ |

The proof of `Filter.limsup_eq_iInf_iSup` is short. Write $L$ for the infimum of the eventual upper bounds. For $s \in f$, the element $\sup_{x \in s} u(x)$ is an eventual upper bound, because $u(x)$ is below it for each $x$ in $s$. So $L \le \sup_{x \in s} u(x)$ for each $s \in f$. Conversely, let $a$ be an eventual upper bound. Then $s = \{x \mid u(x) \le a\}$ is in $f$, and $\sup_{x \in s} u(x) \le a$. So the infimum over $s \in f$ is below each eventual upper bound, hence below $L$. The formula for sequences follows with the basis $\{i \mid i \ge n\}$ of `atTop`.

The general inequalities `Filter.limsup_le_iSup` and `Filter.iInf_le_liminf` compare the limits with the global supremum and infimum. `Filter.limsup_const` says that the limit superior of a constant function is the constant, for a filter that is not trivial, and `Filter.limsup_pure` evaluates along the principal ultrafilter of a point.

#### Comparison and the boundedness hypotheses

In a conditionally complete lattice the infimum of an unbounded set is a junk value. So most lemmas carry the hypotheses `Filter.IsBoundedUnder (· ≤ ·) f u` (the function is eventually bounded above) and `Filter.IsCoboundedUnder (· ≤ ·) f u` (the set of eventual upper bounds is bounded below). The two hypotheses are auto parameters that the tactic `isBoundedDefault` fills in a complete lattice. In `ℝ` the user must give them.

The comparison lemmas follow one naming pattern.

1. `Filter.limsup_le_limsup` gives $\limsup_f u \le \limsup_f v$ from $u \le v$ eventually, and `Filter.liminf_le_liminf` is the dual.
2. `Filter.limsup_le_of_le` gives $\limsup_f u \le a$ from $u \le a$ eventually, and `Filter.le_limsup_of_frequently_le` gives $a \le \limsup_f u$ from $a \le u$ frequently.
3. `Filter.limsup_le_limsup_of_le` compares two filters: a finer filter has a smaller limit superior.
4. `Filter.limsup_congr` says that two functions that agree eventually have the same limit superior.

The main inequality is `Filter.liminf_le_limsup`: for a filter $f$ that is not trivial, and $u$ bounded above and below along $f$, $\liminf_f u \le \limsup_f u$. The idea of the proof: if $a \le u(x)$ eventually and $u(x) \le b$ eventually, then the intersection of the two sets of $f$ is not empty, because $f \neq \bot$. A point $x$ in it gives $a \le u(x) \le b$. So each eventual lower bound is below each eventual upper bound, and the supremum of the first set is below the infimum of the second.

In a conditionally complete linear order, the lemmas `Filter.frequently_lt_of_lt_limsup` and `Filter.eventually_lt_of_limsup_lt` give the two characteristic properties. If $b < \limsup_f u$, then $b < u(x)$ frequently. If $\limsup_f u < b$, then $u(x) < b$ eventually. The proof of the first is by contraposition: if $u(x) \le b$ eventually, then $b$ is an eventual upper bound, so $\limsup_f u \le b$. The equivalences `Filter.limsup_le_iff` and `Filter.le_limsup_iff` restate these facts with a quantifier over all $y > x$ or $y < x$.

#### Limits of sets

For a family of sets $s : \iota \to \operatorname{Set} \alpha$, the lattice `Set α` is a complete Boolean algebra, so no bound hypothesis is needed. The lemma `Filter.mem_limsup_iff_frequently_mem` says that $a \in \limsup_f s$ if and only if $a \in s(i)$ frequently for $f$. Dually, `Filter.mem_liminf_iff_eventually_mem` gives "eventually". For the cofinite filter, `Filter.cofinite.limsup_set_eq` gives the classical description
$$\limsup s = \{ x \mid \{ n \mid x \in s(n) \} \text{ is infinite} \},$$
and `Filter.cofinite.liminf_set_eq` gives the set of the points that lie in all but finitely many $s(n)$. The proof of `Filter.mem_limsup_iff_frequently_mem` uses the formula of a complete lattice: $a$ is in $\bigcap_{t \in f} \bigcup_{i \in t} s(i)$ if and only if each $t \in f$ has an $i$ with $a \in s(i)$, and this is the definition of "frequently".

#### Lattice operations

In a complete Boolean algebra the complement exchanges the two limits: `Filter.limsup_compl` says $(\limsup_f u)^c = \liminf_f u^c$, and `Filter.liminf_compl` is the dual. The proof uses the formula of a complete lattice and the De Morgan laws for infinite suprema and infima. The lemmas `Filter.limsup_sdiff` and `Filter.sdiff_limsup` move a difference through the limit.

In a complete distributive lattice, `Filter.sup_limsup` gives $a \sqcup \limsup_f u = \limsup_f (a \sqcup u)$, and `Filter.limsup_sup_filter` gives $\limsup_{f \sqcup g} u = \limsup_f u \sqcup \limsup_g u$. For the bounded forms, `Filter.blimsup_or_eq_sup` splits a disjunction of predicates into a supremum. In a linear order, `limsup_max` gives the limit superior of a pointwise maximum. For maps, `OrderIso.limsup_apply` moves an order isomorphism through the limit, and `Filter.limsup_comp` turns a composition into a limit along the image filter. `CompleteLatticeHom.apply_limsup_iterate` says that the limit superior of the orbit of $a$ under a complete lattice morphism $g$ is a fixed point of $g$.

#### Common errors

1. In `ℝ`, the limit superior of a sequence that is not bounded above is a junk value, not $+\infty$. A statement with infinite values needs `EReal` or `ENNReal`, which are complete lattices, so that the bound hypotheses go away.
2. The bound hypotheses of a lemma such as `Filter.limsup_le_of_le` are auto parameters. In a complete lattice they are silent. In `ℝ` the tactic `isBoundedDefault` fails and the error names the missing `Filter.IsCoboundedUnder` goal, which the user must prove with an explicit bound.
3. The inequality `Filter.liminf_le_limsup` needs `f.NeBot`. Along the bottom filter, `Filter.limsup_bot` gives $\bot$ and the dual gives $\top$, so the inequality fails.

### Exercises

1. (A) Compute the limit superior and the limit inferior of the sequence $u_n = (-1)^n$ in `EReal` with `Filter.limsup_eq_iInf_iSup_of_nat` and its dual.
2. (A) Use `Filter.limsup_le_limsup` to prove that $\limsup_n u_n \le \limsup_n v_n$ for two bounded real sequences with $u_n \le v_n$ for $n \ge 10$.
3. (B) Prove `Filter.limsup_eq_iInf_iSup` from `Filter.limsup_eq` in a complete lattice.
4. (B) Prove that the limit superior of the sets $A_n = \{ k \in \mathbb{N} \mid k \text{ divides } n \}$ along `Filter.atTop` is the set of the positive integers, with `Filter.mem_limsup_iff_frequently_mem`.
5. (B) Show that $\liminf_n A_n \subseteq \limsup_n A_n$ for each sequence of sets, and give an example where the inclusion is strict.
6. (C) For a real sequence bounded above and below, prove that $\liminf_n u_n = \limsup_n u_n = L$ gives $u_n \to L$, with `Filter.eventually_lt_of_limsup_lt` and its dual.

### Reference

<?reference?>
