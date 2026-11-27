---
title: Newton's map
kind: theory
modules:
  - Mathlib.Dynamics.Newton
explains:
  E3: [Polynomial.newtonMap, Polynomial.isFixedPt_newtonMap_of_isUnit_iff, Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero]
  E2: [Polynomial.newtonMap_apply, Polynomial.newtonMap_apply_of_isUnit, Polynomial.newtonMap_apply_of_not_isUnit, Polynomial.isFixedPt_newtonMap_of_aeval_eq_zero, Polynomial.aeval_pow_two_pow_dvd_aeval_iterate_newtonMap, Polynomial.isNilpotent_iterate_newtonMap_sub_of_isNilpotent]
  E1: auto
families: []
requires: [V06, V07, V15]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Newton's map

### Overview

Newton's method finds a root of a function by iteration of the map $N(x) = x - P(x)/P'(x)$. The roots of $P$ are fixed points of $N$, and near a simple root the iterates converge very fast: the number of correct digits doubles at each step. Mathlib has the algebraic form of this map. It works in a commutative ring, where "near a root" means that $P(x)$ is nilpotent, and there the iteration reaches an exact root after finitely many steps. This form gives Hensel's lemma for rings such as $\mathbb{Z}/p^k\mathbb{Z}$ and the Jordan-Chevalley decomposition of a linear map. The section uses the fixed points of Section 1, polynomials from Volume 6, Chapter 5, and Taylor's theorem from Volume 15, Chapter 4.

### Definitions

**Definition (Newton's map over the reals).** Let $P$ be a differentiable function on an interval with $P' \neq 0$. *Newton's map* is $N(x) = x - P(x)/P'(x)$. The point $N(x)$ is the zero of the tangent line of $P$ at $x$.

**Definition (Nilpotent element).** An element $a$ of a ring is *nilpotent* if $a^k = 0$ for some $k \ge 1$. In a commutative ring, the sum of two nilpotent elements is nilpotent (by the binomial theorem, $(a + b)^{k + l} = 0$ when $a^k = 0 = b^l$), a multiple of a nilpotent element is nilpotent, and $u + a$ is a unit when $u$ is a unit and $a$ is nilpotent (Exercise 2).

**Definition (Newton's map of a polynomial).** Let $R$ be a commutative ring, $S$ a commutative $R$-algebra and $P \in R[X]$ with derivative $P'$. For $x \in S$, put
$$N_P(x) = \begin{cases} x - P'(x)^{-1} P(x) & \text{if } P'(x) \text{ is a unit of } S, \\ x & \text{otherwise.} \end{cases}$$

::: mathlib
`Polynomial.newtonMap` · `Mathlib.Dynamics.Newton`

`P.newtonMap : S → S` is `fun x ↦ x - Ring.inverse (aeval x (derivative P)) * aeval x P`. The function `Ring.inverse` is the inverse on units and `0` elsewhere, so the second case of the definition is a junk value: `newtonMap_apply_of_not_isUnit` gives `P.newtonMap x = x`. With a proof `h` that `P'(x)` is a unit, `newtonMap_apply_of_isUnit h` gives the first case with `h.unit⁻¹`.

<?decl Polynomial.newtonMap?>
:::

### Theorems and proofs

**Theorem (Quadratic convergence).** Let $P$ be twice continuously differentiable on $I = [r - \delta, r + \delta]$, with $P(r) = 0$, $|P'| \ge m > 0$ and $|P''| \le M$ on $I$. Put $C = M/(2m)$ and suppose $C\delta < 1$. For $x_0 \in I$ and $x_{n+1} = N(x_n)$, all $x_n$ lie in $I$ and
$$|x_{n+1} - r| \le C\, |x_n - r|^2, \qquad |x_n - r| \le \frac{(C|x_0 - r|)^{2^n}}{C}.$$

*Proof.* Let $x \in I$. Taylor's theorem with the Lagrange remainder gives $\xi$ between $x$ and $r$ with
$$0 = P(r) = P(x) + P'(x)(r - x) + \tfrac{1}{2}P''(\xi)(r - x)^2.$$
Divide by $P'(x)$ and reorder: $N(x) - r = x - P(x)/P'(x) - r = \dfrac{P''(\xi)}{2P'(x)}(x - r)^2$. So $|N(x) - r| \le C|x - r|^2 \le C\delta\, |x - r| \le |x - r|$, and $N(x) \in I$. By induction all $x_n$ lie in $I$, and the first inequality holds. Put $e_n = C|x_n - r|$. Then $e_{n+1} \le e_n^2$, so $e_n \le e_0^{2^n}$, which is the second inequality. Since $e_0 \le C\delta < 1$, $x_n \to r$. $\square$

The index of this edition has no declaration for Newton's method over $\mathbb{R}$. It has only the algebraic form below.

**Theorem (Roots are the fixed points).** If $P(x) = 0$, then $N_P(x) = x$. If $P'(x)$ is a unit, then $N_P(x) = x$ if and only if $P(x) = 0$.

*Proof.* If $P'(x)$ is not a unit, then $N_P(x) = x$ by definition. If $u = P'(x)$ is a unit, then $N_P(x) = x$ if and only if $u^{-1}P(x) = 0$, and multiplication by the unit $u$ shows that this holds if and only if $P(x) = 0$. Both claims follow. $\square$

::: mathlib
`Polynomial.isFixedPt_newtonMap_of_isUnit_iff` · `Mathlib.Dynamics.Newton`

`IsUnit (aeval x (derivative P)) → (IsFixedPt P.newtonMap x ↔ aeval x P = 0)`. The first claim, with no hypothesis on `P'(x)`, is `isFixedPt_newtonMap_of_aeval_eq_zero`.

<?decl Polynomial.isFixedPt_newtonMap_of_isUnit_iff?>
:::

**Lemma (Taylor expansion in a ring).** For $P \in R[X]$ and $x, h \in S$ there is $Q \in S$ with $P(x + h) = P(x) + P'(x)h + h^2 Q$. Also $h$ divides $P(x + h) - P(x)$ and $P'(x + h) - P'(x)$.

*Proof.* Both sides are $R$-linear in $P$, so it is sufficient to take $P = X^k$. The binomial theorem gives $(x + h)^k = x^k + k x^{k-1} h + h^2 \sum_{i \ge 2} \binom{k}{i} x^{k-i} h^{i-2}$, and $P'(x) = k x^{k-1}$. The two divisibilities follow from the first formula, applied to $P$ and to $P'$. $\square$

**Theorem (Newton's method for a nilpotent defect).** Let $x \in S$ with $P(x)$ nilpotent and $P'(x)$ a unit. Put $x_n = N_P^{[n]}(x)$ and $a = P(x)$. Then for each $n$:

1. $x_n - x$ is nilpotent and $P'(x_n)$ is a unit;
2. $a^{2^n}$ divides $P(x_n)$.

If $a^k = 0$ and $2^n \ge k$, then $P(x_n) = 0$. There is exactly one $r \in S$ with $x - r$ nilpotent and $P(r) = 0$.

*Proof.* Use induction on $n$. For $n = 0$ both claims hold. Suppose them for $n$, and let $u = P'(x_n)$. By claim 2, $P(x_n)$ is a multiple of the nilpotent $a$, so it is nilpotent. Put $h = -u^{-1}P(x_n)$, so that $x_{n+1} = x_n + h$ and $h$ is nilpotent. Then $x_{n+1} - x = (x_n - x) + h$ is nilpotent. By the lemma, $P'(x_{n+1}) = P'(x) + (x_{n+1} - x)w$ for some $w$, a unit plus a nilpotent, so a unit. This is claim 1. For claim 2, the lemma gives
$$P(x_{n+1}) = P(x_n) + u h + h^2 Q = h^2 Q = u^{-2} P(x_n)^2 Q,$$
because $uh = -P(x_n)$. Since $a^{2^n}$ divides $P(x_n)$, $a^{2^{n+1}}$ divides $P(x_{n+1})$.

If $2^n \ge k$, then $a^{2^n} = 0$, so $P(x_n) = 0$. Then $r = x_n$ is a root with $x - r$ nilpotent. For uniqueness, let $r$ and $s$ be two such roots and $d = r - s = (x - s) - (x - r)$, a nilpotent. As in claim 1, $P'(s)$ is a unit. The lemma at $s$ gives $0 = P(r) - P(s) = d\,(P'(s) + dQ)$. The factor $P'(s) + dQ$ is a unit plus a nilpotent, so a unit, and $d = 0$. $\square$

::: mathlib
`Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero` · `Mathlib.Dynamics.Newton`

`IsNilpotent (aeval x P) → IsUnit (aeval x (derivative P)) → ∃! r, IsNilpotent (x - r) ∧ aeval r P = 0`. The steps are `isNilpotent_iterate_newtonMap_sub_of_isNilpotent`, claim 1 without the hypothesis on `P'(x)` (if `P'(x)` is not a unit, the map fixes `x`), and `aeval_pow_two_pow_dvd_aeval_iterate_newtonMap`, claim 2. The Taylor lemma in Mathlib is `Polynomial.binomExpansion` for evaluation in `R`, and `Polynomial.aeval_add_of_sq_eq_zero` for the case `h ^ 2 = 0`.

<?decl Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero?>
:::

### Examples

**Example (The square root of 2).** For $P(x) = x^2 - 2$, $N(x) = (x + 2/x)/2$, the Babylonian method. From $x_0 = 1$ the iterates are $1.5$, $1.416667$, $1.4142157$, $1.41421356237469$. The errors are about $8.6 \cdot 10^{-2}$, $2.5 \cdot 10^{-3}$, $2.1 \cdot 10^{-6}$ and $1.6 \cdot 10^{-12}$: each error is about $0.35$ times the square of the one before, and $1/(2\sqrt 2) \approx 0.354$.

**Example (Hensel's lemma modulo 25).** Let $P = X^2 + 1 \in \mathbb{Z}[X]$ and $S = \mathbb{Z}/25\mathbb{Z}$. For $x = 2$, $P(2) = 5$ is nilpotent, since $5^2 = 0$ in $S$, and $P'(2) = 4$ is a unit with inverse $19$, since $4 \cdot 19 = 76 = 1 + 3 \cdot 25$. One step gives $N_P(2) = 2 - 19 \cdot 5 = -93 = 7$ in $S$, and indeed $7^2 + 1 = 50 = 0$ in $S$. One step suffices because $a^2 = 0$ for $a = 5$. The uniqueness says that $7$ is the only square root of $-1$ in $S$ that is $2$ modulo $5$.

**Example (A Jordan-Chevalley decomposition).** Let
$$A = \begin{pmatrix} 1 & 1 & 0 \\ 0 & 1 & 0 \\ 0 & 0 & 2 \end{pmatrix}$$
over $\mathbb{Q}$, with minimal polynomial $(X - 1)^2(X - 2)$. Take its squarefree part $P = (X - 1)(X - 2)$ and $S = \mathbb{Q}[A]$, a commutative ring. A computation gives $P(A) = (A - I)(A - 2I) = -E_{12}$, where $E_{12}$ is the matrix unit, so $P(A)^2 = 0$. Also $P'(A) = 2A - 3I$ has inverse $\begin{pmatrix} -1 & -2 & 0 \\ 0 & -1 & 0 \\ 0 & 0 & 1 \end{pmatrix}$, and $P'(A)^{-1}P(A) = E_{12}$. So $N_P(A) = A - E_{12} = \operatorname{diag}(1, 1, 2)$. This is the semisimple part $s$, a root of the squarefree $P$, and $A - s = E_{12}$ is the nilpotent part.

### The library around it

The last example is the general proof. Let $f$ be a linear map of a finite-dimensional space over a perfect field $K$, and $P$ the squarefree part of its minimal polynomial. Then $P(f)$ is nilpotent. Over a perfect field $P$ is separable, so $aP + bP' = 1$ for some polynomials $a, b$. Then $b(f)P'(f) = 1 - a(f)P(f)$ is a unit of $K[f]$. The theorem gives $s \in K[f]$ with $P(s) = 0$ and $f - s$ nilpotent, and $s$ is semisimple because a separable polynomial annihilates it. Mathlib states the result as `Module.End.exists_isNilpotent_isSemisimple` in `Mathlib.LinearAlgebra.JordanChevalley`.

<?decl Module.End.exists_isNilpotent_isSemisimple?>

Common errors of a learner:

- `newtonMap` exists for each `x`; at a point where `P'(x)` is not a unit it is the identity, so a fixed point of the map need not be a root.
- The nilpotent theorem needs `S` commutative. The two summands of the decomposition commute because both lie in `K[f]`.

### Exercises

1. (A) Write Newton's map for $P = X^3 - 2$ and compute two steps from $x_0 = 1$.
2. (A) Let $a^k = 0$ in a commutative ring. Show that $1 - a$ is a unit with inverse $1 + a + \cdots + a^{k-1}$. Deduce that $u + a$ is a unit for each unit $u$.
3. (B) Find the square root of $-1$ in $\mathbb{Z}/125\mathbb{Z}$ that is $2$ modulo $5$. Hint: two steps of $N_P$ from $x = 2$, since $5^3 = 0$ and $2^2 \ge 3$.
4. (B) For $P(x) = x^3$ show that Newton's map is $N(x) = 2x/3$, and that the convergence to the triple root $0$ is only linear. Find the hypothesis of the quadratic theorem that fails.
5. (B) Let $P$ have a double root. Show that the nilpotent theorem cannot apply at a root $x$ of $P$, and find the hypothesis that fails.
6. (C) Find the Jordan-Chevalley decomposition of $\begin{pmatrix} 2 & 1 \\ -1 & 0 \end{pmatrix}$ over $\mathbb{Q}$ by Newton's map.

### Notes and history

Newton described the method for polynomials around 1669, and Raphson gave the form with successive substitutions in 1690. The form $x - P(x)/P'(x)$ with the derivative came later. Hensel's lemma for $p$-adic numbers is a form of the nilpotent theorem.

### Reference

<?reference?>
