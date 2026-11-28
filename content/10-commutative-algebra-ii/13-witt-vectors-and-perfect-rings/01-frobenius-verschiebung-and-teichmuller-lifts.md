---
title: Frobenius, Verschiebung and Teichmüller lifts
kind: api
modules:
  - Mathlib.RingTheory.WittVector.StructurePolynomial
  - Mathlib.RingTheory.WittVector.IsPoly
  - Mathlib.RingTheory.WittVector.Frobenius
  - Mathlib.RingTheory.WittVector.Verschiebung
  - Mathlib.RingTheory.WittVector.Identities
  - Mathlib.RingTheory.WittVector.MulP
  - Mathlib.RingTheory.WittVector.Teichmuller
  - Mathlib.RingTheory.WittVector.TeichmullerSeries
  - Mathlib.RingTheory.WittVector.InitTail
  - Mathlib.RingTheory.WittVector.MulCoeff
explains:
  E2: [wittStructureInt, wittStructureInt_existsUnique, WittVector.IsPoly, WittVector.frobenius, WittVector.coeff_frobenius_charP, WittVector.verschiebung, WittVector.frobenius_verschiebung, WittVector.teichmuller, WittVector.init, WittVector.nth_mul_coeff]
  E1: auto
families: []
requires: [V10.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Frobenius, Verschiebung and Teichmüller lifts

### Overview

Chapter 8 defines the ring $W(R)$ of $p$-typical Witt vectors through the Witt polynomials $w_n = \sum_{i=0}^n p^i X_i^{p^{n-i}}$ and the ghost map. This section describes the operations on $W(R)$ that the rest of the theory uses. There are three of them.

1. The Frobenius $F : W(R) \to W(R)$ is a ring map with $w_n(Fx) = w_{n+1}(x)$. In characteristic $p$ it raises each coordinate to the power $p$.
2. The Verschiebung $V : W(R) \to W(R)$ is additive and shifts the coordinates: $V(x_0, x_1, \dots) = (0, x_0, x_1, \dots)$.
3. The Teichmüller map $r \mapsto [r] = (r, 0, 0, \dots)$ is multiplicative.

The main identity is $F(V(x)) = px$ for each ring $R$. In characteristic $p$, also $V(F(x)) = px$. For a perfect ring of characteristic $p$, each Witt vector has a unique expansion $x = \sum_i [r_i]p^i$.

Behind these operations is a general principle. A ring operation on Witt vectors is defined by integer polynomials in the coordinates. To prove an identity between such operations, it is enough to prove it after the ghost map over a ring in which $p$ is invertible. Mathlib makes this principle a class, `WittVector.IsPoly`, with a tactic that uses it.

### The library around it

#### Structure polynomials

The ring operations of $W(R)$ come from one theorem.

**Theorem.** Let $p$ be a prime and let $\Phi \in \mathbb{Z}[X_i : i \in I]$. There is a unique family $\varphi_n \in \mathbb{Z}[X_{i,k} : i \in I, k \in \mathbb{N}]$ such that $w_n(\varphi_0, \dots, \varphi_n) = \Phi(w_n(X_{i,\cdot}))$ for each $n$.

This is `wittStructureInt_existsUnique` in `Mathlib.RingTheory.WittVector.StructurePolynomial`, and the polynomials are `wittStructureInt p Φ n`.

*Proof sketch.* Over $\mathbb{Q}$, the polynomial $w_n$ has the form $p^nX_n + (\text{terms in } X_0, \dots, X_{n-1})$. So the equations can be solved for $\varphi_n$ by recursion, with a division by $p^n$. This gives `wittStructureRat`, with the recursion `wittStructureRat_rec`. The hard step is to show that the coefficients are integers. The key congruence is `C_p_pow_dvd_bind₁_rename_wittPolynomial_sub_sum`: the difference between the right side and the known part of the left side is divisible by $p^n$ over $\mathbb{Z}$. Then `map_wittStructureInt` identifies the integer family with the rational one. $\square$

For $\Phi = X_0 + X_1$ and $\Phi = X_0X_1$ this gives the addition and multiplication polynomials `WittVector.wittAdd` and `WittVector.wittMul` of Chapter 8. The lemma `wittStructureInt_vars` says that $\varphi_n$ uses only the variables $X_{i,k}$ with $k \le n$. So the first $n + 1$ coordinates of a sum or product depend only on the first $n + 1$ coordinates of the inputs.

#### Polynomial functions and the ghost argument

A function $f$ that is defined for each ring $R$, with $f : W(R) \to W(R)$, is polynomial if there are integer polynomials $\varphi_n$ with $f(x)_n = \varphi_n(x_0, x_1, \dots)$ for all $R$ and $x$. The class `WittVector.IsPoly p f` in `Mathlib.RingTheory.WittVector.IsPoly` states this, and `WittVector.IsPoly₂` is the form for two arguments. Instances are provided for $0$, $1$, negation, addition and multiplication, and for compositions, `WittVector.IsPoly.comp` and `WittVector.IsPoly₂.comp`.

Two facts make the class useful.

1. A polynomial function commutes with each map $W(g)$ for a ring map $g$. This is `WittVector.IsPoly.map`.
2. The polynomials of $f$ are determined by their images under the Witt polynomials, `WittVector.poly_eq_of_wittPolynomial_bind_eq`.

The tactic ghost_calc reduces an identity between polynomial functions to the case of a ring in which $p$ is invertible. There the ghost map is a bijection, `WittVector.ghostEquiv`, and the identity becomes an identity of sequences in $R^{\mathbb{N}}$. The tactic ghost_simp then simplifies the ghost components.

The module `Mathlib.RingTheory.WittVector.MulP` gives multiplication by a natural number $n$ as a polynomial function. The polynomials are `WittVector.wittMulN p n k`, and `WittVector.mulN_coeff` gives the coordinates of $x \cdot n$.

#### Frobenius

The module `Mathlib.RingTheory.WittVector.Frobenius` defines the Frobenius polynomials `WittVector.frobeniusPoly`. They are the unique integer polynomials with $w_n(\varphi_0, \dots, \varphi_n) = w_{n+1}$, by `WittVector.bind₁_frobeniusPoly_wittPolynomial`. This gives `WittVector.frobenius`, a ring map $W(R) \to W(R)$ with ghost components shifted by one, `WittVector.ghostComponent_frobenius`.

The coefficients of `WittVector.frobeniusPoly` are integers, although the recursion over $\mathbb{Q}$ divides by powers of $p$. Modulo $p$, the polynomial is $X_n^p$, `WittVector.frobeniusPoly_zmod`. So for a ring of characteristic $p$, the Frobenius of $W(R)$ is the map $W(\operatorname{Frob})$ that raises each coordinate to the power $p$. This is `WittVector.coeff_frobenius_charP` and `WittVector.frobenius_eq_map_frobenius`. If $R$ is perfect, then $F$ is bijective, `WittVector.frobenius_bijective`, with the ring isomorphism `WittVector.frobeniusEquiv`. On $W(\mathbb{F}_p) = \mathbb{Z}_p$, the Frobenius is the identity, `WittVector.frobenius_zmodp`.

#### Verschiebung

The module `Mathlib.RingTheory.WittVector.Verschiebung` defines `WittVector.verschiebung`, an additive map with coordinates $0, x_0, x_1, \dots$. The lemmas `WittVector.verschiebung_coeff_zero` and `WittVector.verschiebung_coeff_succ` give these coordinates. The ghost components satisfy $w_0(Vx) = 0$ and $w_{n+1}(Vx) = p\,w_n(x)$, `WittVector.ghostComponent_verschiebung`. The map is injective, `WittVector.verschiebung_injective`, but it is not a ring map: $V(1) \ne 1$.

#### Identities

The module `Mathlib.RingTheory.WittVector.Identities` proves the relations between $F$, $V$ and $p$.

| Lean name | Statement | Hypothesis |
|---|---|---|
| `WittVector.frobenius_verschiebung` | $F(V(x)) = px$ | none |
| `WittVector.verschiebung_mul_frobenius` | $V(x \cdot F(y)) = V(x) \cdot y$ | none |
| `WittVector.verschiebung_frobenius` | $V(F(x)) = px$ | characteristic $p$ |
| `WittVector.verschiebung_frobenius_comm` | $V \circ F = F \circ V$ | characteristic $p$ |
| `WittVector.coeff_p` | $p = (0, 1, 0, 0, \dots)$ | characteristic $p$ |
| `WittVector.mul_charP_coeff_succ` | $(px)_{i+1} = x_i^p$ | characteristic $p$ |

The first identity follows from the ghost argument: $w_n(FVx) = w_{n+1}(Vx) = p\,w_n(x) = w_n(px)$. In characteristic $p$, the second and third give multiplication by $p$ as the shift with $p$-th powers: $px = (0, x_0^p, x_1^p, \dots)$. The lemma `WittVector.verschiebung_zmod` gives $V(x) = px$ over $\mathbb{Z}/p$.

#### Teichmüller lifts

The module `Mathlib.RingTheory.WittVector.Teichmuller` defines `WittVector.teichmuller p : R →* 𝕎 R`. Its coordinates are $r, 0, 0, \dots$, by `WittVector.teichmuller_coeff_zero` and `WittVector.teichmuller_coeff_pos`, and its ghost components are $r^{p^n}$, `WittVector.ghostComponent_teichmuller`. The map is multiplicative, but not additive. It is a section of the zeroth coordinate `WittVector.constantCoeff`, which is a ring map onto $R$.

**Theorem.** Let $R$ be a perfect ring of characteristic $p$ and $x \in W(R)$. For each $n$, $x - \sum_{i \le n} [x_i^{p^{-i}}]p^i$ is divisible by $p^{n+1}$.

This is `WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff` in `Mathlib.RingTheory.WittVector.TeichmullerSeries`. The proof uses `WittVector.teichmuller_mul_pow_coeff`: the only nonzero coordinate of $[r]p^n$ is $r^{p^n}$ in position $n$. So $[x_i^{p^{-i}}]p^i$ has coordinate $x_i$ in position $i$, and a sum of Witt vectors with disjoint supports is computed coordinate by coordinate, `WittVector.sum_coeff_eq_coeff_sum`.

#### Initial segments and the product formula

The module `Mathlib.RingTheory.WittVector.InitTail` defines `WittVector.init n x`, which keeps the first $n$ coordinates and puts $0$ in the others, and `WittVector.tail n x`, which keeps the other coordinates. Their sum is $x$, `WittVector.init_add_tail`. The lemmas `WittVector.init_add` and `WittVector.init_mul` say that `init n` of a sum or product depends only on `init n` of the inputs. A tactic, init_ring, proves these statements.

The module `Mathlib.RingTheory.WittVector.MulCoeff` isolates the top coordinate of a product.

**Theorem.** Let $R$ have characteristic $p$. There is a function $f$ of the first $n + 1$ coordinates of $x$ and $y$ such that $(xy)_{n+1} = x_{n+1}y_0^{p^{n+1}} + y_{n+1}x_0^{p^{n+1}} + f$. This is `WittVector.nth_mul_coeff`.

This formula is the tool for solving equations in $W(k)$ coordinate by coordinate, for example in the next section.

#### Common errors

1. `WittVector.verschiebung_frobenius` and `WittVector.coeff_p` need `CharP R p`. Over $\mathbb{Z}$ the Witt vector $p$ is not $(0, 1, 0, \dots)$, since its zeroth coordinate is $p$.
2. `WittVector.teichmuller` is a `MonoidHom`, not a ring map. The lift of $r + s$ differs from $[r] + [s]$ in the higher coordinates.
3. `WittVector.verschiebung` is an `AddMonoidHom` only. The rule for products is `WittVector.verschiebung_mul_frobenius`, not multiplicativity.

### Exercises

1. (A) Use `WittVector.ghostComponent_frobenius` and `WittVector.ghostComponent_verschiebung` to compute the ghost components of $F(V(x))$, and deduce $F(V(x)) = px$ over a ring in which $p$ is invertible.
2. (A) Compute `WittVector.frobeniusPoly p 0` and check that it is $X_0^p + pX_1$.
3. (B) Show that in characteristic $p$, $px = (0, x_0^p, x_1^p, \dots)$, from `WittVector.verschiebung_frobenius` and `WittVector.coeff_frobenius_charP`.
4. (B) Show that $[r][s] = [rs]$ by a computation of ghost components, and show for $p = 2$ that $[1] + [1] \ne [2]$ in $W(\mathbb{F}_2)$.
5. (B) Show that the zeroth coordinate is a ring map $W(R) \to R$ with kernel the image of $V$.
6. (C) Let $k$ be a perfect field of characteristic $p$. Use the Teichmüller expansion to show that each element of $W(k)$ that is not divisible by $p$ is a unit.

### Reference

<?reference?>
