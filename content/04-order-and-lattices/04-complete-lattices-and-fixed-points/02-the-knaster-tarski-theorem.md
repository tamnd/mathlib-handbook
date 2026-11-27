---
title: The Knaster-Tarski theorem
kind: theory
modules:
  - Mathlib.Order.FixedPoints
explains:
  E3: [OrderHom.lfp, OrderHom.gfp, fixedPoints.completeLattice]
  E2: [OrderHom.map_lfp, OrderHom.lfp_le, OrderHom.lfp_induction, fixedPoints.lfp_eq_sSup_iterate, OmegaCompletePartialOrder.ωScottContinuous]
  E1: auto
families: []
requires: [V04.C02, V04.C03]
reads_with: ["MIL"]
lean:
  - MathlibHandbook/V04/C04/Examples.lean
  - MathlibHandbook/V04/C04/Exercises.lean
  - MathlibHandbook/V04/C04/Solutions.lean
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The Knaster-Tarski theorem

### Overview

Many objects of mathematics are the smallest set that contains some elements and is closed under some rules. The natural numbers are the smallest set that contains $0$ and is closed under $n \mapsto n + 1$. Each of these is the least fixed point of a monotone map on a complete lattice.

The theorem of Knaster and Tarski says that each monotone map on a complete lattice has a least and a greatest fixed point, and gives formulas for them. Tarski proved more: the fixed points form a complete lattice. This section proves both statements, derives the induction principle for the least fixed point, proves the theorem of Cantor, Schröder and Bernstein, and ends with the theorem of Kleene, which computes the least fixed point by iteration from $\bot$.

### Definitions

Let $P$ be a complete lattice and let $f : P \to P$ be monotone.

**Definition (Fixed points).** An element $a \in P$ is a *fixed point* of $f$ if $f(a) = a$. It is a *prefixed point* if $f(a) \le a$, and a *postfixed point* if $a \le f(a)$.

In the lattice of subsets, a prefixed point is a set $A$ with $f(A) \subseteq A$: a set that is *closed* under the rule $f$. The top $\top$ is always a prefixed point, and $\bot$ is always a postfixed point.

**Definition (Least and greatest fixed points).** The *least fixed point* of $f$ is $\operatorname{lfp} f = \inf \{ a \in P \mid f(a) \le a \}$, the infimum of the prefixed points. The *greatest fixed point* is $\operatorname{gfp} f = \sup \{ a \in P \mid a \le f(a) \}$, the supremum of the postfixed points.

**Definition (Chains and continuity).** An *$\omega$-chain* in $P$ is a sequence $c_0 \le c_1 \le c_2 \le \cdots$. A monotone map $f$ is *$\omega$-continuous* if $f(\bigsqcup_n c_n) = \bigsqcup_n f(c_n)$ for each $\omega$-chain $(c_n)$.

A monotone map always satisfies $\bigsqcup_n f(c_n) \le f(\bigsqcup_n c_n)$, since $c_n \le \bigsqcup_m c_m$ gives $f(c_n) \le f(\bigsqcup_m c_m)$. So $\omega$-continuity asks only for the other inequality.

::: mathlib
`OrderHom.lfp` · `Mathlib.Order.FixedPoints`

The least fixed point takes a bundled monotone map `f : α →o α`. Then `lfp` is itself a monotone map `(α →o α) →o α`: a larger map has a larger least fixed point. The definition is `sInf {a | f a ≤ a}`, as in the text. For a function `g` with `hg : Monotone g`, write `OrderHom.lfp ⟨g, hg⟩`.

<?decl OrderHom.lfp?>
:::

::: mathlib
`OrderHom.gfp` · `Mathlib.Order.FixedPoints`

The greatest fixed point is `sSup {a | a ≤ f a}`. Mathlib proves its lemmas from those for `lfp` in the dual order `αᵒᵈ`. The lemmas `OrderHom.map_gfp` and `OrderHom.le_gfp` are the duals of `OrderHom.map_lfp` and `OrderHom.lfp_le`.

<?decl OrderHom.gfp?>
:::

::: mathlib
`OmegaCompletePartialOrder.ωScottContinuous` · `Mathlib.Order.OmegaCompletePartialOrder`

Mathlib states continuity for $\omega$-complete partial orders, in which only the chains need suprema. A complete lattice is such an order. The lemma `ωScottContinuous.monotone` shows that a continuous map is monotone.

<?decl OmegaCompletePartialOrder.ωScottContinuous?>
:::

### Theorems and proofs

**Theorem (Knaster-Tarski).** Let $P$ be a complete lattice and let $f : P \to P$ be monotone. Let $m = \operatorname{lfp} f$. Then:

1. $f(m) = m$;
2. $m \le a$ for each prefixed point $a$, so in particular $m \le x$ for each fixed point $x$;
3. dually, $M = \operatorname{gfp} f$ is a fixed point, and $a \le M$ for each postfixed point $a$.

*Proof.* Let $S = \{ a \in P \mid f(a) \le a \}$, so $m = \inf S$. Claim 2 is immediate: $m$ is a lower bound of $S$.

For claim 1, first show $f(m) \le m$. Let $a \in S$. Then $m \le a$, so $f(m) \le f(a)$ by monotonicity, and $f(a) \le a$ because $a \in S$. So $f(m)$ is a lower bound of $S$, and $f(m) \le m$.

Next show $m \le f(m)$. Monotonicity applied to $f(m) \le m$ gives $f(f(m)) \le f(m)$, so $f(m) \in S$. Then $m \le f(m)$, because $m$ is a lower bound of $S$. Antisymmetry gives $f(m) = m$.

A fixed point $x$ satisfies $f(x) \le x$, so $x \in S$ and $m \le x$. Claim 3 is claims 1 and 2 for $f$ on the dual lattice $P^{\mathrm{op}}$, where the prefixed points are the postfixed points of $P$. $\square$

So $\operatorname{lfp} f$ is the least prefixed point. To show $\operatorname{lfp} f \le a$, it suffices to show $f(a) \le a$. In the lattice of sets, this is the principle of induction: a set closed under the rule contains the set that the rule generates.

::: mathlib
`OrderHom.map_lfp` · `Mathlib.Order.FixedPoints`

The lemma states `f (lfp f) = lfp f`, claim 1. The Lean proof is the paper proof. The form `OrderHom.isLeast_lfp` states that `lfp f` is the least fixed point.

<?decl OrderHom.map_lfp?>
:::

::: mathlib
`OrderHom.lfp_le` · `Mathlib.Order.FixedPoints`

The lemma takes `h : f a ≤ a` and gives `lfp f ≤ a`, claim 2. The lemma `OrderHom.le_lfp` gives a lower bound: if `a` is below each prefixed point, then `a ≤ lfp f`.

<?decl OrderHom.lfp_le?>
:::

The next theorem is a stronger induction principle, for a property that is not an inequality.

**Theorem (Induction for the least fixed point).** Let $p$ be a property of the elements of $P$. Assume:

1. if $p(a)$ and $a \le \operatorname{lfp} f$, then $p(f(a))$;
2. if $p(a)$ for each $a$ in a set $T$, then $p(\sup T)$.

Then $p(\operatorname{lfp} f)$.

*Proof.* Let $m = \operatorname{lfp} f$, let $T = \{ a \in P \mid a \le m \text{ and } p(a) \}$ and let $b = \sup T$. Each member of $T$ satisfies $p$, so $p(b)$ by hypothesis 2. Each member of $T$ is below $m$, so $b \le m$. Hypothesis 1 with $p(b)$ and $b \le m$ gives $p(f(b))$. Monotonicity gives $f(b) \le f(m) = m$. So $f(b) \in T$, and $f(b) \le b$. Thus $b$ is a prefixed point, and the Knaster-Tarski theorem gives $m \le b$. So $b = m$, and $p(m)$ holds. $\square$

Hypothesis 2 for $T = \emptyset$ gives $p(\bot)$. So the property holds at the start, passes through $f$, and passes to suprema.

::: mathlib
`OrderHom.lfp_induction` · `Mathlib.Order.FixedPoints`

The statement is the theorem above, with the hypotheses in the same order. The dual is `OrderHom.gfp_induction`.

<?decl OrderHom.lfp_induction?>
:::

**Theorem (Tarski: the fixed points form a complete lattice).** Let $P$ be a complete lattice and let $f : P \to P$ be monotone. Then the set $F = \{ x \in P \mid f(x) = x \}$, with the order of $P$, is a complete lattice. In particular $F$ is not empty.

*Proof.* By the theorem "Suprema give infima" of the previous section, it suffices to show that each $S \subseteq F$ has a supremum in $F$. Let $b = \sup S$ in $P$ and $Q = \{ x \in P \mid b \le x \}$.

$Q$ is a complete lattice. Let $T \subseteq Q$. If $T$ is not empty, then $\sup T$ is above a member of $T$, which is above $b$, so $\sup T \in Q$ is the supremum of $T$ in $Q$. If $T$ is empty, its supremum in $Q$ is the least element $b$ of $Q$. So $Q$ is a complete lattice by the theorem of the previous section.

$f$ maps $Q$ to $Q$. Let $x \in Q$. For each $s \in S$, $s \le x$, so $s = f(s) \le f(x)$. So $f(x)$ is an upper bound of $S$, $b \le f(x)$ and $f(x) \in Q$.

By the Knaster-Tarski theorem, the restriction of $f$ to $Q$ has a least fixed point $c$. Then $c \in F$. It is an upper bound of $S$, since $s \le b \le c$ for each $s \in S$. Let $x \in F$ be an upper bound of $S$. Then $b \le x$, so $x$ is a fixed point in $Q$ and $c \le x$. So $c$ is the least upper bound of $S$ in $F$. $\square$

The supremum in $F$ is the least fixed point above $\sup S$, and in general it is not $\sup S$, as an example below shows. For $S = \emptyset$ the proof gives $c = \operatorname{lfp} f$, the bottom of $F$.

::: mathlib
`fixedPoints.completeLattice` · `Mathlib.Order.FixedPoints`

The instance puts a `CompleteLattice` structure on the subtype `Function.fixedPoints f`. The supremum of a set of fixed points is `OrderHom.nextFixed`, the least fixed point above the supremum in `α`, and the infimum is `OrderHom.prevFixed`, the greatest fixed point below the infimum in `α`. The order is the order of `α`, but the supremum is not, so the lemmas on `sSup` in `α` do not apply.

<?decl fixedPoints.completeLattice?>
:::

**Theorem (Cantor-Schröder-Bernstein).** Let $f : A \to B$ and $g : B \to A$ be injective maps. Then there is a bijection $h : A \to B$.

*Proof.* Define $\Phi : \mathcal{P}(A) \to \mathcal{P}(A)$ by $\Phi(S) = A \setminus g(B \setminus f(S))$. It is monotone: if $S \subseteq T$, then $f(S) \subseteq f(T)$, so $B \setminus f(T) \subseteq B \setminus f(S)$, so $g(B \setminus f(T)) \subseteq g(B \setminus f(S))$, and the complements satisfy $\Phi(S) \subseteq \Phi(T)$.

Let $S = \operatorname{lfp} \Phi$. Then $S = \Phi(S)$, so $A \setminus S = g(B \setminus f(S))$. For $x \in A \setminus S$ there is a $y \in B \setminus f(S)$ with $g(y) = x$, unique because $g$ is injective. Write $y = g^{-1}(x)$. Define $h(x) = f(x)$ for $x \in S$ and $h(x) = g^{-1}(x)$ for $x \in A \setminus S$.

$h$ is injective. Let $h(x) = h(x')$. If $x, x' \in S$, then $f(x) = f(x')$ and $x = x'$. If $x, x' \notin S$, then $g^{-1}(x) = g^{-1}(x')$, and applying $g$ gives $x = x'$. If $x \in S$ and $x' \notin S$, then $h(x) \in f(S)$ and $h(x') \in B \setminus f(S)$, so they are different, and this case does not occur.

$h$ is surjective. Let $y \in B$. If $y \in f(S)$, then $y = f(x)$ for some $x \in S$, and $h(x) = y$. If $y \notin f(S)$, let $x = g(y)$. Then $x \in g(B \setminus f(S)) = A \setminus S$, so $h(x) = g^{-1}(x) = y$. $\square$

::: mathlib
`Function.Embedding.schroeder_bernstein` · `Mathlib.SetTheory.Cardinal.SchroederBernstein`

The Lean proof is the proof above. It takes `OrderHom.lfp` of the monotone map `s ↦ (g '' (f '' s)ᶜ)ᶜ` on `Set α` and builds the bijection with `Set.piecewise` and `Function.invFun g`.

<?decl Function.Embedding.schroeder_bernstein?>
:::

The formula for $\operatorname{lfp} f$ takes the infimum of a set that contains the unknown answer. Kleene's theorem builds the least fixed point from below when $f$ is continuous.

**Theorem (Kleene).** Let $P$ be a complete lattice and let $f : P \to P$ be monotone and $\omega$-continuous. Then $\operatorname{lfp} f = \bigsqcup_{n \ge 0} f^n(\bot)$, where $f^0(\bot) = \bot$ and $f^{n+1}(\bot) = f(f^n(\bot))$.

*Proof.* Write $c_n = f^n(\bot)$ and $c = \bigsqcup_n c_n$.

Step 1: the $c_n$ form a chain. By induction on $n$: $c_0 = \bot \le c_1$, and if $c_n \le c_{n+1}$, then $c_{n+1} = f(c_n) \le f(c_{n+1}) = c_{n+2}$.

Step 2: $c$ is a fixed point. By continuity, $f(c) = \bigsqcup_n f(c_n) = \bigsqcup_n c_{n+1}$. This equals $\bigsqcup_n c_n$, since the only extra member $c_0 = \bot$ is below everything. So $f(c) = c$.

Step 3: $c$ is below each prefixed point. Let $f(a) \le a$. By induction, $c_n \le a$: $\bot \le a$, and if $c_n \le a$, then $c_{n+1} = f(c_n) \le f(a) \le a$. So $c \le a$.

By Step 3, $c \le \operatorname{lfp} f$, since $\operatorname{lfp} f$ is a prefixed point. By Step 2, $c$ is a prefixed point, so $\operatorname{lfp} f \le c$. Thus $c = \operatorname{lfp} f$. $\square$

Step 3 does not use continuity, so $\bigsqcup_n f^n(\bot) \le \operatorname{lfp} f$ for every monotone $f$. The counterexample below shows that the equality can fail without continuity.

::: mathlib
`fixedPoints.lfp_eq_sSup_iterate` · `Mathlib.Order.FixedPoints`

The hypothesis is `ωScottContinuous f` for `f : α →o α`, and the conclusion is `f.lfp = ⨆ n, f^[n] ⊥`, where `f^[n]` is the `n`-fold composite. The dual is `fixedPoints.gfp_eq_sInf_iterate`.

<?decl fixedPoints.lfp_eq_sSup_iterate?>
:::

### Examples

**Example (A fixed point in Lean).** The least fixed point of a bundled monotone map is a fixed point.

<?lean MathlibHandbook/V04/C04/Examples.lean#lfp?>

**Example (The least fixed point is least).** To prove a property of `lfp f`, find an element $a$ with the property and with $f(a) \le a$.

<?lean MathlibHandbook/V04/C04/Examples.lean#lfp_le?>

**Example (The reachable vertices of a graph).** Let $V = \{1, 2, 3, 4, 5\}$ with the directed edges $1 \to 2$, $2 \to 3$, $3 \to 1$, $4 \to 5$ and $5 \to 4$. Let $R(X) = \{1\} \cup \{ w \mid v \to w \text{ for some } v \in X \}$ on the subsets of $V$. The map $R$ is monotone and preserves unions, so Kleene's theorem applies. The iterates are
$$R^0(\emptyset) = \emptyset,\quad R^1(\emptyset) = \{1\},\quad R^2(\emptyset) = \{1, 2\},\quad R^3(\emptyset) = \{1, 2, 3\},\quad R^4(\emptyset) = \{1, 2, 3\}.$$
So $\operatorname{lfp} R = \{1, 2, 3\}$, the vertices reachable from $1$. But $R(V) = \{1\} \cup \{2, 3, 1, 5, 4\} = V$, so $\operatorname{gfp} R = V$. The gfp also contains the cycle $4 \to 5 \to 4$, which never meets $1$: a gfp collects the elements that the rules do not exclude, an lfp only the elements that the rules produce.

**Example (The supremum of fixed points is not the union).** Let $P$ be the subsets of $\{1, 2, 3\}$, and let $f(X) = X \cup \{3\}$ if $\{1, 2\} \subseteq X$, and $f(X) = X$ otherwise. The map is monotone. If $X \subseteq Y$ and $\{1, 2\} \subseteq X$, then $\{1, 2\} \subseteq Y$ and $f(X) = X \cup \{3\} \subseteq f(Y)$. Otherwise $f(X) = X \subseteq Y \subseteq f(Y)$. The sets $\{1\}$ and $\{2\}$ are fixed points, but $f(\{1, 2\}) = \{1, 2, 3\}$. In the lattice of fixed points, $\{1\} \sqcup \{2\} = \{1, 2, 3\}$, the least fixed point above $\{1, 2\}$.

**Counterexample (Kleene needs continuity).** Let $P = \{0, 1, 2, \dots\} \cup \{\omega, \omega + 1\}$ with $0 < 1 < 2 < \cdots < \omega < \omega + 1$. A finite set has its largest element as supremum, an infinite set of natural numbers has $\omega$, and a set that contains $\omega$ or $\omega + 1$ has its largest element. So $P$ is a complete lattice. Let $f(n) = n + 1$ and $f(\omega) = f(\omega + 1) = \omega + 1$. Then $f$ is monotone, and its only fixed point is $\omega + 1$. The iterates are $f^n(0) = n$, with supremum $\omega \neq \operatorname{lfp} f$. Here $f(\bigsqcup_n n) = f(\omega) = \omega + 1$, but $\bigsqcup_n f(n) = \omega$, so $f$ is not continuous.

### The library around it

The file `Mathlib.Order.FixedPoints` has the characterizations `map_lfp`, `lfp_le`, `le_lfp`, `isLeast_lfp` and their duals, the comparison `lfp_le_gfp`, and the rolling rule `OrderHom.map_lfp_comp`: `f (lfp (g.comp f)) = lfp (f.comp g)`. The namespace `fixedPoints` has the lattice of fixed points and the iteration formulas. The predicate `Function.IsFixedPt` is for any function. Lean's inductive types give many least fixed points directly.

### Exercises

1. (A) Find the least and the greatest fixed points of $X \mapsto X \cup \{0\}$ on the subsets of $\mathbb{N}$. *Hint:* list the fixed points first.
2. (A) Compute $\operatorname{lfp}$ and $\operatorname{gfp}$ of the constant map $x \mapsto a$ on a complete lattice.
3. (B) Show that $\operatorname{lfp} f \le \operatorname{gfp} f$ without the dual theorem. *Hint:* $\operatorname{lfp} f$ is a postfixed point.
4. (B) Let $f \le g$ pointwise, both monotone. Show that $\operatorname{lfp} f \le \operatorname{lfp} g$. *Hint:* a prefixed point of $g$ is a prefixed point of $f$.
5. (B) Let $G$ be a group and $A \subseteq G$. Write the subgroup generated by $A$ as the least fixed point of a monotone map on the subsets of $G$, and compute the first three iterates of Kleene's theorem for $G = \mathbb{Z}$ and $A = \{4, 6\}$.
6. (B) Show that a monotone map on a finite lattice is $\omega$-continuous, and that the iteration from $\bot$ reaches $\operatorname{lfp} f$ after finitely many steps.
7. (C) Show that the postfixed points of a monotone $f$ are closed under the suprema of $P$, and conclude that they form a complete lattice with the order of $P$. *Hint:* if $a_i \le f(a_i)$ for each $i$, then $a_i \le f(\bigsqcup_j a_j)$.
8. (C) Let $A = \mathbb{N}$, $B = \mathbb{N} \setminus \{0\}$, $f(n) = n + 1$ and let $g : B \to A$ be the inclusion. Follow the proof of Cantor-Schröder-Bernstein: compute $\Phi(S)$, find $\operatorname{lfp} \Phi$ with Kleene's theorem, and write $h$. *Hint:* $\Phi(S) = \{0\} \cup f(S)$.
9. (L) Prove that the least fixed point is below the greatest fixed point. The solution is `lfp_le_gfp_example`.

### Notes and history

Knaster and Tarski proved the theorem for the lattice of subsets of a set in 1928, in the paper of Knaster *Un théorème sur les fonctions d'ensembles*. Tarski proved the general form, with the lattice of fixed points, in the Pacific Journal of Mathematics 5 (1955). In the same volume Anne Davis proved the converse: a lattice in which every monotone map has a fixed point is complete. The iteration formula is usually named after Kleene. In Mathlib, the file `Mathlib.Order.FixedPoints` is by Johannes Hölzl, Kenny Lau and Yury Kudryashov, and `Mathlib.SetTheory.Ordinal.FixedPointApproximants` builds the least fixed point of a map that is not continuous by ordinal iteration.

### Reference

<?reference?>
