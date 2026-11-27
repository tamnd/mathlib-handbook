---
title: Fixed points and recursion
kind: theory
modules:
  - Mathlib.Control.Fix
  - Mathlib.Control.LawfulFix
explains:
  E3: [Fix, Part.Fix.approx, Part.fix, Part.fix_def, Part.fix_def', LawfulFix, Part.Fix.approx_mono, Part.Fix.mem_iff, Part.fix_eq_ωSup, Part.fix_le, Part.fix_eq_of_ωScottContinuous, Part.lawfulFix]
  E2: [Fix.fix, Part.hasFix, Pi.Part.hasFix, Part.fixAux, Part.Fix.approx_mono', Part.Fix.approxChain, Part.Fix.approx_le_fix, Part.Fix.exists_fix_le_approx, Part.Fix.le_f_of_mem_approx, Part.fix_eq_ωSup_of_ωScottContinuous, LawfulFix.fix_eq, Part.toUnitMono, Part.ωScottContinuous_toUnitMono, Pi.lawfulFix, Pi.hasFix, Pi.lawfulFix', Pi.monotoneCurry, Pi.monotoneUncurry, Pi.ωScottContinuous_curry, Pi.ωScottContinuous_uncurry]
  E1: auto
families: []
requires: [V01.C04, V04.C02, V04.C04, V33.C04]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Fixed points and recursion

### Overview

Lean accepts a recursive definition when it can see that the recursion ends: by structural recursion on an inductive type, or by well-founded recursion with a proof that some measure decreases. Many programs do not fit. The function that counts the steps of the Collatz iteration $n \mapsto n/2$ for even $n$ and $n \mapsto 3n + 1$ for odd $n$ has no known proof of termination, and an interpreter for a programming language can run forever on some inputs. Such a function is still meaningful as a partial function: it has a value where the computation stops and no value where it runs forever.

Domain theory gives the method. A recursive definition $g = F(g)$ is read as an equation for a fixed point of a functional $F$ on partial functions. The partial functions form an $\omega$-complete partial order, the totally undefined function is its least element, and the least fixed point is the limit of the approximations $\bot, F(\bot), F(F(\bot)), \ldots$ (the Kleene construction). Mathlib packs this in two classes. `Fix α` has an operator `fix : (α → α) → α` with no law. `LawfulFix α` asks for the equation `fix f = f (fix f)` for every $\omega$-Scott-continuous $f$. The instances use `Part`, the type of possibly undefined values, and functions into `Part`. This section builds the fixed point, proves that it is the least fixed point, and computes three examples by hand.

### Definitions

**Definition (Fix).** The class `Fix α` has one field, `fix : (α → α) → α`. It states no property: an instance only chooses an element for each function $\alpha \to \alpha$.

**Definition (Part and its order).** An element of `Part α` is a proposition `Dom` with a value `get : Dom → α`. It is `some a` when `Dom` holds and `get` gives $a$, and `none` when `Dom` is false. Write $a \in x$ when $x$ is defined with value $a$. The order is $x \le y$ if and only if every $a \in x$ is also in $y$: $y$ is at least as defined as $x$ and agrees with it. So `none` is the least element $\bot$, and `some a ≤ some b` holds only for $a = b$. On functions `∀ a, Part (β a)`, the order is pointwise.

**Definition (Chains and ω-continuity).** A chain in a partial order is a monotone sequence $c_0 \le c_1 \le \cdots$. An $\omega$-complete partial order (`OmegaCompletePartialOrder`) has a least upper bound $\omega\mathrm{Sup}\,c$ for every chain. In `Part α`, a chain is `none` for a while and then constant with one value $a$, or `none` for ever; $\omega\mathrm{Sup}\,c$ is `some a` in the first case and `none` in the second (`Part.ωSup_eq_some` and `Part.ωSup_eq_none`). For functions into `Part`, $\omega\mathrm{Sup}$ is taken pointwise. A function $f$ between such orders is $\omega$-Scott-continuous (`ωScottContinuous f`) if it is monotone and $f(\omega\mathrm{Sup}\,c) = \omega\mathrm{Sup}(f \circ c)$ for every chain $c$.

**Definition (Approximations).** For $f \colon (\forall a, \mathrm{Part}(\beta\,a)) \to (\forall a, \mathrm{Part}(\beta\,a))$, the approximations are the stream $$\mathrm{approx}\,f\,0 = \bot, \qquad \mathrm{approx}\,f\,(i + 1) = f(\mathrm{approx}\,f\,i).$$ So $\mathrm{approx}\,f\,i = f^{i}(\bot)$. When $f$ is monotone, `Part.Fix.approxChain f` is this sequence as a chain.

**Definition (The fixed point of Part).** For $f$ as above and a point $x$, $$\mathrm{Part.fix}\,f\,x = \mathrm{assert}\,(\exists i,\ (\mathrm{approx}\,f\,i\,x).\mathrm{Dom})\ (\ldots).$$ If some approximation is defined at $x$, the value is computed by a loop over $i = 0, 1, 2, \ldots$ (the function `Part.fixAux`, with well-founded recursion on `Nat.Upto`) that stops at the first $i$ where the approximation is defined. If no approximation is defined at $x$, the value is `none`. The definition needs no property of $f$.

The instances are `Pi.Part.hasFix : Fix (α → Part β)` with `fix = Part.fix`, `Part.hasFix : Fix (Part α)`, which reads `Part α` as `Unit → Part α`, and `Pi.hasFix` for curried functions of two arguments through `Sigma`.

**Definition (Lawful fixed point operator).** For an $\omega$-complete partial order $\alpha$, the class `LawfulFix α` extends `Fix α` with `fix_eq : ωScottContinuous f → fix f = f (fix f)`.

The law is not asked for every $f$. The counterexample below shows that no operator can satisfy it for all $f$.

### Theorems and proofs

**Lemma (Unfolding of the fixed point).** If $\exists i,\ (\mathrm{approx}\,f\,i\,x).\mathrm{Dom}$ and $N$ is the least such $i$, then $\mathrm{Part.fix}\,f\,x = \mathrm{approx}\,f\,(N + 1)\,x$. If there is no such $i$, then $\mathrm{Part.fix}\,f\,x = \mathrm{none}$.

*Proof.* The second claim is the definition, since `assert p g` is `none` when $p$ is false. For the first, the loop starts at $i = 0$. At step $i$ it evaluates $f$ on the function that is undefined at every point if the approximation $i$ is already defined at $x$, and that calls step $i + 1$ otherwise. By induction on $N - i$, the result of step $i$ is $\mathrm{approx}\,f\,(N + 1 - i)$ applied to the current point. At $i = N$ the approximation is defined, so the loop evaluates $f(\bot) = \mathrm{approx}\,f\,1$; below $N$ it is not defined, so step $i$ is $f$ of step $i + 1$, which is $f(\mathrm{approx}\,f\,(N - i)) = \mathrm{approx}\,f\,(N + 1 - i)$. At $i = 0$ this gives $\mathrm{approx}\,f\,(N + 1)\,x$. $\square$

These are `Part.fix_def` and `Part.fix_def'`. The loop needs well-founded recursion because the index $i$ goes up. `Nat.Upto p` is the type of $i$ such that no $j < i$ satisfies $p$. When $p$ holds somewhere, the relation $j > i$ on it is well-founded, since no index can pass the first point where $p$ holds.

**Lemma (The approximations increase).** If $f$ is monotone, then $\mathrm{approx}\,f\,i \le \mathrm{approx}\,f\,j$ for $i \le j$.

*Proof.* First $\mathrm{approx}\,f\,i \le \mathrm{approx}\,f\,(i + 1)$ by induction on $i$. For $i = 0$, $\bot \le f(\bot)$ since $\bot$ is the least element. For the step, $\mathrm{approx}\,f\,i \le \mathrm{approx}\,f\,(i + 1)$ and monotonicity give $f(\mathrm{approx}\,f\,i) \le f(\mathrm{approx}\,f\,(i + 1))$, which is $\mathrm{approx}\,f\,(i + 1) \le \mathrm{approx}\,f\,(i + 2)$. For $i \le j$, apply this $j - i$ times and use transitivity. $\square$

**Proposition (Membership in the fixed point).** If $f$ is monotone, then $b \in \mathrm{Part.fix}\,f\,a$ if and only if $b \in \mathrm{approx}\,f\,i\,a$ for some $i$.

*Proof.* Suppose first that some approximation is defined at $a$, with least index $N$. By the unfolding lemma, $\mathrm{Part.fix}\,f\,a = \mathrm{approx}\,f\,(N + 1)\,a$. So $b \in \mathrm{Part.fix}\,f\,a$ gives the claim with $i = N + 1$. Conversely, let $b \in \mathrm{approx}\,f\,i\,a$. The approximation $N$ is defined at $a$ with some value $y$, and by the lemma above $y \in \mathrm{approx}\,f\,(N + 1)\,a$. Put $k = \max(i, N + 1)$. By monotonicity, both $b$ and $y$ are in $\mathrm{approx}\,f\,k\,a$. An element of `Part` has at most one value, so $b = y$, and $b \in \mathrm{Part.fix}\,f\,a$. Suppose now that no approximation is defined at $a$. Then $\mathrm{Part.fix}\,f\,a = \mathrm{none}$ has no element, and no $\mathrm{approx}\,f\,i\,a$ has an element. $\square$

This is `Part.Fix.mem_iff`. It gives at once `Part.Fix.approx_le_fix`: each approximation is below the fixed point.

**Theorem (Fixed point as a supremum).** If $f$ is monotone, then $\mathrm{Part.fix}\,f = \omega\mathrm{Sup}(\mathrm{approxChain}\,f)$.

*Proof.* Both sides are functions, so compare them at a point $a$, and use antisymmetry. Each $\mathrm{approx}\,f\,i$ is below $\mathrm{Part.fix}\,f$, so the least upper bound is below $\mathrm{Part.fix}\,f$. For the other inequality, let $b \in \mathrm{Part.fix}\,f\,a$. By the proposition, $b \in \mathrm{approx}\,f\,i\,a$ for some $i$, so the chain at $a$ contains `some b` and its supremum at $a$ is `some b`. $\square$

**Theorem (Least prefixed point).** If $f$ is monotone and $f(X) \le X$, then $\mathrm{Part.fix}\,f \le X$.

*Proof.* By the previous theorem, it is enough to show $\mathrm{approx}\,f\,i \le X$ for all $i$. Induction on $i$: $\mathrm{approx}\,f\,0 = \bot \le X$, and if $\mathrm{approx}\,f\,i \le X$ then $\mathrm{approx}\,f\,(i + 1) = f(\mathrm{approx}\,f\,i) \le f(X) \le X$ by monotonicity and the hypothesis. $\square$

This is `Part.fix_le`. Each fixed point $X$ satisfies $f(X) \le X$, so `Part.fix f` is below every fixed point. It is the least fixed point once the next theorem shows that it is a fixed point.

**Theorem (Kleene fixed point for Part).** If $g$ is $\omega$-Scott-continuous, then $\mathrm{Part.fix}\,g = g(\mathrm{Part.fix}\,g)$.

*Proof.* Let $c = \mathrm{approxChain}\,g$, so $c_i = \mathrm{approx}\,g\,i$. By the supremum theorem and continuity, $$g(\mathrm{Part.fix}\,g) = g(\omega\mathrm{Sup}\,c) = \omega\mathrm{Sup}(g \circ c).$$ The chain $g \circ c$ is $c_1, c_2, c_3, \ldots$, the chain $c$ without its first term. It has the same supremum as $c$. Every $c_i$ is below $c_{i + 1} = g(c_i)$, so $\omega\mathrm{Sup}\,c \le \omega\mathrm{Sup}(g \circ c)$. Every $g(c_i)$ is the term $c_{i + 1}$ of $c$, so $\omega\mathrm{Sup}(g \circ c) \le \omega\mathrm{Sup}\,c$. So $g(\mathrm{Part.fix}\,g) = \omega\mathrm{Sup}\,c = \mathrm{Part.fix}\,g$. $\square$

This is `Part.fix_eq_of_ωScottContinuous`, and it gives the instance `Pi.lawfulFix : LawfulFix (α → Part β)`. For `Part α`, the instance `Part.lawfulFix` reads an element as a function on `Unit` with `Part.toUnitMono` and checks that this preserves continuity. For curried functions, `Pi.lawfulFix'` uses that `Sigma.curry` and `Sigma.uncurry` are continuous (`Pi.ωScottContinuous_curry` and `Pi.ωScottContinuous_uncurry`).

**Counterexample (A function with no fixed point).** On `Part Unit`, define $h(x) = \mathrm{none}$ if $x$ is defined and $h(x) = \mathrm{some}\,()$ if $x$ is `none`. The only elements are `none` and `some ()`. Now $h(\mathrm{none}) = \mathrm{some}\,() \ne \mathrm{none}$ and $h(\mathrm{some}\,()) = \mathrm{none} \ne \mathrm{some}\,()$, so $h$ has no fixed point. So no operator on `Part Unit` satisfies `fix h = h (fix h)` for all $h$. The function $h$ is not monotone: $\mathrm{none} \le \mathrm{some}\,()$, but $h(\mathrm{none}) = \mathrm{some}\,()$ is not below $h(\mathrm{some}\,()) = \mathrm{none}$. This is the function of the halting problem, defined exactly when its argument is not, and it is the reason for the hypothesis of continuity in `LawfulFix`.

### Examples

**Example (Factorial by fix).** Let $F\,g\,n = \mathrm{some}\,1$ for $n = 0$ and $F\,g\,n = (\lambda v.\, n \cdot v) \mathbin{<\$>} g(n - 1)$ for $n > 0$. The approximations at small values are:

- $\mathrm{approx}\,1\,0 = F\,\bot\,0 = \mathrm{some}\,1$, and $\mathrm{approx}\,1\,n = \mathrm{none}$ for $n > 0$;
- $\mathrm{approx}\,2\,1 = 1 \cdot 1 = \mathrm{some}\,1$;
- $\mathrm{approx}\,3\,2 = 2 \cdot 1 = \mathrm{some}\,2$;
- $\mathrm{approx}\,4\,3 = 3 \cdot 2 = \mathrm{some}\,6$.

By induction, $\mathrm{approx}\,i\,3 = \mathrm{none}$ for $i \le 3$. So the least index with a defined value at $3$ is $N = 4$, and by the unfolding lemma $\mathrm{Part.fix}\,F\,3 = \mathrm{approx}\,5\,3 = \mathrm{some}\,6$. In general, $\mathrm{approx}\,i\,n$ is defined exactly when $i \ge n + 1$, with value $n!$.

**Example (A Collatz-style function).** The step counter is a fixed point with no proof of termination:

```lean
noncomputable def collatzSteps : ℕ → Part ℕ :=
  Fix.fix fun g n =>
    if n ≤ 1 then Part.some 0
    else (g (if n % 2 = 0 then n / 2 else 3 * n + 1)).map (· + 1)
```

For $n = 6$, the orbit is $6, 3, 10, 5, 16, 8, 4, 2, 1$, with $8$ steps. The approximation $\mathrm{approx}\,i\,n$ is defined exactly when the orbit of $n$ reaches $1$ in at most $i - 1$ steps: one application of the functional is used at each of the $8$ points $6, 3, \ldots, 2$, and one more at $1$. So $\mathrm{approx}\,i\,6$ is defined for $i \ge 9$ with value $8$, and $\mathrm{collatzSteps}\,6 = \mathrm{some}\,8$. If some $n$ has an orbit that never reaches $1$, then $\mathrm{collatzSteps}\,n = \mathrm{none}$. The definition is the same in both cases, and Lean does not need to know which case occurs.

The functional is $\omega$-Scott-continuous. It is monotone, and at each point $n > 1$ its value depends on $g$ at one point $m$ only. For a chain $c$, $b \in (\omega\mathrm{Sup}\,c)(m)$ if and only if $b \in c_i(m)$ for some $i$ (`Part.mem_ωSup`), and so $b + 1$ is in the functional applied to $\omega\mathrm{Sup}\,c$ at $n$ if and only if it is in the functional applied to some $c_i$. So `LawfulFix.fix_eq` applies and gives the recursion equation `collatzSteps 6 = (collatzSteps 3).map (· + 1)`.

**Example (A function that loops).** Let $F\,g\,n = g(n + 1)$. Then $\mathrm{approx}\,0 = \bot$, and if $\mathrm{approx}\,i = \bot$ then $\mathrm{approx}\,(i + 1)\,n = \mathrm{approx}\,i\,(n + 1) = \mathrm{none}$. So all approximations are $\bot$, and $\mathrm{Part.fix}\,F = \bot$ by `Part.fix_def'`. The equation $g\,n = g(n + 1)$ has many solutions, such as every constant function `fun _ => some 7`. The fixed point operator picks the least one, the function that is nowhere defined. With $F\,g = g$ every function is a fixed point, and again $\mathrm{Part.fix}\,F = \bot$.

### The library around it

::: mathlib
`Part.fix` · `Mathlib.Control.Fix`

The class `Fix` with `Fix.fix`, the approximations `Part.Fix.approx`, the loop `Part.fixAux`, the operator `Part.fix`, and the lemmas `Part.fix_def` and `Part.fix_def'`. The instances are `Part.hasFix` and `Pi.Part.hasFix`. The file depends on `Part`, `Nat.find` and `Nat.Upto`, and not on order theory.

<?decl Part.fix?>
:::

::: mathlib
`Part.fix_eq_of_ωScottContinuous` · `Mathlib.Control.LawfulFix`

The class `LawfulFix` with `LawfulFix.fix_eq`. For a monotone $f$: `Part.Fix.approx_mono'`, `approx_mono`, `mem_iff`, `approx_le_fix`, `exists_fix_le_approx`, `approxChain` and `le_f_of_mem_approx`, then `Part.fix_eq_ωSup` and `Part.fix_le`. For a continuous $g$: `Part.fix_eq_ωSup_of_ωScottContinuous` and `Part.fix_eq_of_ωScottContinuous`. The instances are `Part.lawfulFix`, `Pi.lawfulFix` and `Pi.lawfulFix'`, with the helpers `Part.toUnitMono`, `Pi.monotoneCurry` and `Pi.monotoneUncurry`.

<?decl Part.fix_eq_of_ωScottContinuous?>
:::

::: mathlib
`OmegaCompletePartialOrder.fixedPoints.ωSup_iterate_mem_fixedPoint` · `Mathlib.Order.OmegaCompletePartialOrder`

The Kleene theorem for any $\omega$-complete partial order: for a continuous map $f$ and a point $x \le f(x)$, the supremum of the chain $x, f(x), f^2(x), \ldots$ (`fixedPoints.iterateChain`) is a fixed point, and `ωSup_iterate_le_prefixedPoint` shows that it is below each prefixed point above $x$. The same file defines `ωScottContinuous`, `Chain`, the order on `Part` with `Part.ωSup`, `Part.mem_ωSup` and `Part.ωSup_eq_some`, and the pointwise order on functions.

<?decl OmegaCompletePartialOrder.fixedPoints.ωSup_iterate_mem_fixedPoint?>
:::

::: mathlib
`OrderHom.lfp` · `Mathlib.Order.FixedPoints`

The Knaster-Tarski least fixed point of a monotone map on a complete lattice, with `OrderHom.lfp_le` and `fixedPoints.lfp_eq_sSup_iterate`. It does not apply to `Part α`, which is not a complete lattice: `some 1` and `some 2` in `Part ℕ` have no upper bound. This is why `Control.LawfulFix` works with $\omega$-complete partial orders.

<?decl OrderHom.lfp?>
:::

Common errors of a learner: The first error is to expect `Fix.fix f = f (Fix.fix f)` from the class `Fix`; the class has no law, and the equation needs `LawfulFix` and a proof of continuity. The second error is to expect `decide` to settle whether `Part.fix f x` is defined; its domain is the proposition `∃ i, (approx f i x).Dom`, which can be undecidable, and for the Collatz function nobody knows whether it holds for all $n$. The third error is to expect `Part.fix` to give the intended function when the functional is not monotone; then `Part.fix` is still defined, but the lemmas of this section do not apply. The fourth error is to confuse the least fixed point with the intended one: for $F\,g\,n = g(n + 1)$ every constant function is a fixed point, and `Part.fix` returns the nowhere defined function.

### Exercises

1. (A) Compute $\mathrm{approx}\,i\,2$ for the factorial functional and $i = 0, 1, 2, 3, 4$. Hint: the first defined value appears at $i = 3$.
2. (A) Show that `some 1` and `some 2` have no upper bound in `Part ℕ`. Hint: an upper bound contains both values.
3. (A) For $F\,g\,n = g\,n$, show $\mathrm{approx}\,F\,i = \bot$ for all $i$, and deduce $\mathrm{Part.fix}\,F = \bot$ from `Part.fix_le` with $X = \bot$. Hint: $F(\bot) = \bot$.
4. (B) Compute the orbit of $7$ under the Collatz step, and find $\mathrm{collatzSteps}\,7$ and the least $i$ with $\mathrm{approx}\,i\,7$ defined. Hint: the orbit has $16$ steps.
5. (B) Prove that the factorial functional is monotone. Hint: if $g \le g'$ and $v \in g(n - 1)$, then $v \in g'(n - 1)$.
6. (B) Prove that $\mathrm{Part.fix}\,F\,n = \mathrm{some}\,(n!)$ for the factorial functional, by induction on $n$ with `LawfulFix.fix_eq`. Hint: prove continuity as in the Collatz example first.
7. (C) Let $f$ be continuous on an $\omega$-complete partial order with least element $\bot$. Prove that the supremum of $\bot, f(\bot), f^2(\bot), \ldots$ is the least fixed point of $f$. Hint: follow the proofs of `Part.fix_eq_of_ωScottContinuous` and `Part.fix_le` with `fixedPoints.iterateChain`.

### Notes and history

The least fixed point construction by iteration from the bottom element is the Kleene fixed point theorem, and the use of partial orders and continuous functions as meanings of recursive programs is the domain theory of Scott. The construction in Mathlib follows this pattern with `Part` as the domain. The docstring of `LawfulFix` explains the restriction to continuous functions with the counterexample of a function that is defined exactly when its argument is not.

The Mathlib files are by these authors, read from their headers: `Mathlib.Control.Fix` and `Mathlib.Control.LawfulFix` by Simon Hudon.

### Reference

<?reference?>
