---
title: Diophantine sets
kind: api
modules:
  - Mathlib.NumberTheory.Dioph
explains:
  E2: [Dioph, Dioph.DiophFn, Dioph.inter, Dioph.union, Dioph.ex_dioph, Dioph.dvd_dioph, Dioph.pow_dioph, Poly.sumsq_eq_zero]
  E1: auto
families: []
requires: [V02.C02, V32]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Diophantine sets

### Overview

A Diophantine equation asks for the natural number solutions of a polynomial equation with integer coefficients. The sections before this one solve particular equations: $x^2 + y^2 = z^2$, $x^4 + y^4 = z^2$, $x^2 - dy^2 = 1$. This section turns the question around. It asks which sets of natural numbers are described by a polynomial equation with extra unknowns. A set $S \subseteq \mathbb{N}^k$ is *Diophantine* if there is an integer polynomial $p$ in $k + m$ variables with
$$v \in S \iff \exists t \in \mathbb{N}^m,\ p(v, t) = 0.$$
For example, the set of composite numbers is Diophantine, with the polynomial $v - (t_1 + 2)(t_2 + 2)$.

Hilbert's tenth problem asks for an algorithm that decides whether a given Diophantine equation has a solution. The answer is negative: each recursively enumerable set is Diophantine, and some of these sets are not decidable. The last step of the proof is the theorem of Matiyasevic that the graph of the power function $(a, b, c) \mapsto [a^b = c]$ is Diophantine. The module `Mathlib.NumberTheory.Dioph` defines Diophantine sets and functions, proves the closure properties of the class, and proves Matiyasevic's theorem with the solutions of the Pell equation $x^2 - (a^2 - 1)y^2 = 1$. The full solution of Hilbert's tenth problem is not in the library. The computability side lives in Volume 32.

### The library around it

#### Polynomial functions

The module does not use `MvPolynomial`. It has its own type of integer polynomial functions on $\mathbb{N}^\alpha$, for a type $\alpha$ of variables. The predicate `IsPoly f` says that a function $f : (\alpha \to \mathbb{N}) \to \mathbb{Z}$ is a polynomial. It is an inductive predicate with four constructors: the projections `IsPoly.proj`, the constants `IsPoly.const`, and closure under differences and products, `IsPoly.sub` and `IsPoly.mul`. The closure under negation and sums, `IsPoly.neg` and `IsPoly.add`, follows.

The type `Poly α` is the subtype of the functions with `IsPoly`, and `Poly.isPoly` recovers the predicate. It has a coercion to functions, from the instance `Poly.instFunLike`, so `p v` is the value of $p$ at $v$. Two polynomials are equal when they agree at each point, by `Poly.ext`. The basic polynomials are `Poly.proj i`, the $i$-th variable, and `Poly.const n`. The type is a commutative ring, `Poly.instCommRing`, and the simp lemmas `add_apply`, `sub_apply`, `mul_apply`, `neg_apply`, `Poly.proj_apply` and `Poly.const_apply` evaluate the operations pointwise. The principle `Poly.induction` proves a property of all polynomials from the four constructors. A change of variables $f : \alpha \to \beta$ acts by `Poly.map`, and `Poly.map_apply` says that $(\mathrm{map}\, f\, g)(v) = g(v \circ f)$.

One more function is needed for the closure properties. The sum of squares of a list of polynomials, `Poly.sumsq`, is a polynomial that vanishes exactly where all the polynomials of the list vanish:

| Lean name | Statement |
|---|---|
| `Poly.sumsq_nonneg` | $\sum_i p_i(x)^2 \geq 0$ |
| `Poly.sumsq_eq_zero` | $\sum_i p_i(x)^2 = 0 \iff$ each $p_i(x) = 0$ |

The proof of the second line is the fact that a sum of nonnegative integers is $0$ only when each term is $0$.

#### Diophantine sets

**Definition.** A set `S : Set (α → ℕ)` is Diophantine, `Dioph S`, if there are a type $\beta$ and a polynomial `p : Poly (α ⊕ β)` such that $v \in S$ if and only if $p(v, t) = 0$ for some $t : \beta \to \mathbb{N}$.

The variables in $\beta$ are the *dummy* variables. The pair $(v, t)$ is the function on the sum type $\alpha \oplus \beta$ that is $v$ on $\alpha$ and $t$ on $\beta$. The definition allows any type of dummies. The lemma `Dioph.inject_dummies` shows that the dummies may be moved into any type that contains $\beta$, so the proofs can always use a type such as $\alpha \oplus \mathbb{N}$. A set that needs no dummies is Diophantine by `Dioph.of_no_dummies`, and `Dioph.ext` transports the property along an equality of sets.

**Theorem (Closure).** The Diophantine sets are closed under intersection, union and projection. If $S \subseteq \mathbb{N}^{\alpha \oplus \beta}$ is Diophantine, then so is $\{v \mid \exists x,\ (v, x) \in S\}$.

*Proof.* Let $p$ and $q$ define $S$ and $S'$, with disjoint dummies. Then $p^2 + q^2$ defines $S \cap S'$, by `Poly.sumsq_eq_zero`, and $pq$ defines $S \cup S'$, since $\mathbb{Z}$ has no zero divisors. For the projection, the variables $x$ become further dummies of the same polynomial. $\square$

The three parts are `Dioph.inter`, `Dioph.union` and `Dioph.ex_dioph`, with the special case `Dioph.ex1_dioph` for a single variable and the vector form `Dioph.vec_ex1_dioph`. The finite intersection of a list of Diophantine sets is `Dioph.DiophList.forall`. A change of variables keeps the property: if $S$ is Diophantine, so is $\{v \mid v \circ f \in S\}$, by `Dioph.reindex_dioph`.

#### Diophantine functions

A function $f : \mathbb{N}^\alpha \to \mathbb{N}$ is Diophantine, `Dioph.DiophFn f`, if its graph $\{(v, y) \mid f(v) = y\}$ is a Diophantine subset of $\mathbb{N}^{\mathrm{Option}\,\alpha}$. The extra variable `none` holds the value. Partial functions have the same notion, `Dioph.DiophPFun`, with the graph of `PFun.graph`, and `Dioph.diophFn_iff_pFun` says that the two notions agree on total functions. The domain of a Diophantine partial function is Diophantine, by `Dioph.dom_dioph`.

The basic Diophantine functions are the projections, `Dioph.proj_dioph`, the constants, `Dioph.const_dioph`, and the absolute value of a polynomial, `Dioph.abs_poly_dioph`. Composition keeps the property: `Dioph.diophFn_comp1` substitutes a Diophantine function into a Diophantine set, and `Dioph.diophFn_comp`, `Dioph.dioph_comp` and `Dioph.diophFn_compn` substitute several functions at once. The module then proves that the arithmetic of $\mathbb{N}$ is Diophantine:

| Lean name | Statement |
|---|---|
| `Dioph.add_dioph`, `Dioph.mul_dioph` | $f + g$ and $fg$ are Diophantine |
| `Dioph.sub_dioph` | the truncated difference $f - g$ is Diophantine |
| `Dioph.div_dioph`, `Dioph.mod_dioph` | $f / g$ and $f \bmod g$, with the conventions of `ℕ` |
| `Dioph.le_dioph`, `Dioph.lt_dioph` | $\{v \mid f(v) \leq g(v)\}$ and $\{v \mid f(v) < g(v)\}$ |
| `Dioph.ne_dioph` | $\{v \mid f(v) \neq g(v)\}$ |
| `Dioph.dvd_dioph` | $\{v \mid f(v) \mid g(v)\}$ |
| `Dioph.modEq_dioph` | $\{v \mid f(v) \equiv g(v) \pmod{h(v)}\}$ |

Each proof writes the relation with one or two dummies. For example, $a \leq b$ if and only if $b = a + t$ for some $t \in \mathbb{N}$. For divisibility, $a \mid b$ if and only if $b = at$ for some $t$, and this also holds for $a = 0$, where both sides say $b = 0$. The sets $f < g$ and $f \neq g$ follow from $f + 1 \leq g$ and the union of $f < g$ and $g < f$.

The module has a local notation for these sets and functions, so that a statement such as "the set of $v$ with $v_0 \leq v_1 \cdot v_2$" can be written close to its mathematical form. The notation is scoped to the namespace `Dioph`. Many statements also use vectors `Vector3 ℕ n` and the indices `Fin2 n`, which compute well in the kernel. The lemmas `Dioph.diophFn_vec` and `Dioph.diophPFun_vec` translate between functions on `Option α` and vectors, and `Dioph.proj_dioph_of_nat` gives the projection to a fixed coordinate.

#### Pell's equation and the power function

The proof of Matiyasevic's theorem uses the solutions $(x_n, y_n)$ of $x^2 - (a^2 - 1)y^2 = 1$ for $a > 1$, with $x_n + y_n\sqrt{a^2 - 1} = (a + \sqrt{a^2 - 1})^n$. These are `Pell.xn` and `Pell.yn` of the module `Mathlib.NumberTheory.PellMatiyasevic`. The sequences grow exponentially in $n$, and they satisfy many congruences, so they can express $a^b = c$ by polynomial conditions.

1. `Dioph.pell_dioph`: the set of $(a, n, x, y)$ with $a > 1$, $x = x_n(a)$ and $y = y_n(a)$ is Diophantine. The proof uses the characterization of the solutions in `Mathlib.NumberTheory.PellMatiyasevic`, which is a list of polynomial conditions and congruences in $a, n, x, y$ and some dummies.
2. `Dioph.xn_dioph`: the partial function $(a, n) \mapsto x_n(a)$, defined for $a > 1$, is Diophantine.
3. `Dioph.pow_dioph`: if $f$ and $g$ are Diophantine functions, then so is $v \mapsto f(v)^{g(v)}$.

The third result is the form of Matiyasevic's theorem in the library. Its proof expresses $c = a^b$ through $x_n$ and $y_n$ for a large auxiliary $a'$ and the congruence $x_b(a') - (a' - a)y_b(a') \equiv a^b$ modulo $2a'a - a^2 - 1$, with $c$ smaller than the modulus and with special care for $a = 0$ and $b = 0$. The module `Mathlib.NumberTheory.PellMatiyasevic` proves this equivalence. The two Pell facts above and the closure lemmas then give the Diophantine definition.

#### Common errors

1. `Dioph S` is a statement about a set of functions `α → ℕ`, not about a set of tuples. To use a set of pairs, write it as a set of functions on `Fin2 2` or on another type with two elements.
2. The polynomials of `Poly α` have values in `ℤ`, but the variables range over `ℕ`. A set of integer solutions must first be described with natural number variables, for example by writing each integer as a difference of two natural numbers.
3. `Dioph.sub_dioph` and `Dioph.div_dioph` are about the operations of `ℕ`, with $3 - 5 = 0$ and $5 / 0 = 0$. They are not the operations of `ℤ` or `ℚ`.

### Exercises

1. (A) Show that the set of even numbers and the set of composite numbers are Diophantine, by giving the polynomials.
2. (A) Show that the set $\{(a, b) \mid \gcd(a, b) = 1\}$ is Diophantine. Hint: Bézout's identity with natural numbers $ax = by + 1$ or $by = ax + 1$.
3. (B) Let $p(x, t)$ define a Diophantine set $S$ of positive integers. Show that $S$ is the set of positive values of the polynomial $x(1 - p(x, t)^2)$ on $\mathbb{N}^{1 + m}$.
4. (B) Show that the set of $(a, b, c)$ with $c = \binom{a}{b}$ is Diophantine, given `Dioph.pow_dioph`. Hint: read the base $u$ digits of $(1 + u)^a$ for a large $u$.
5. (C) Show that the set of primes is Diophantine. Hint: $p > 1$ is prime if and only if $\gcd(p, (p - 1)!) = 1$, and the factorial is Diophantine by a digit argument as in Exercise 4.

### Reference

<?reference?>
