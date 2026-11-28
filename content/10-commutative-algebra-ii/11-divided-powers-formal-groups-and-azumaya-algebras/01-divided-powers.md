---
title: Divided powers
kind: api
modules:
  - Mathlib.RingTheory.DividedPowers.Basic
  - Mathlib.RingTheory.DividedPowers.DPMorphism
  - Mathlib.RingTheory.DividedPowers.Padic
  - Mathlib.RingTheory.DividedPowers.RatAlgebra
  - Mathlib.RingTheory.DividedPowers.SubDPIdeal
  - Mathlib.RingTheory.DividedPowerAlgebra.Init
explains:
  E2: [DividedPowers, DividedPowers.factorial_mul_dpow_eq_pow, DividedPowers.RatAlgebra.dividedPowers_unique, DividedPowers.OfSquareZero.dividedPowers, DividedPowers.IsDPMorphism.on_span, DividedPowers.Quotient.dividedPowers, DividedPowerAlgebra.lift, DividedPowers.nilpotent_of_mem_dpIdeal]
  E1: auto
families: []
requires: [V09, V08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Divided powers

### Overview

In a $\mathbb{Q}$-algebra the element $x^n/n!$ makes sense for every $x$. In a ring of characteristic $p$, or over $\mathbb{Z}$, it does not, but many formulas of calculus and of cohomology need it. A divided power structure on an ideal $I$ of a commutative ring $A$ is a family of maps $\gamma_n : I \to A$ that behave like $x \mapsto x^n/n!$. The axioms ask for $\gamma_0(x) = 1$, $\gamma_1(x) = x$, $\gamma_n(x) \in I$ for $n \ge 1$, and the identities that $x^n/n!$ satisfies over $\mathbb{Q}$.

This section covers the structure `DividedPowers`, its first consequences, the examples over a $\mathbb{Q}$-algebra, on square zero and nilpotent ideals and on the ideal $(p)$ of $\mathbb{Z}_p$, the morphisms of divided power ideals, the sub divided power ideals and quotients, and the divided power algebra of a module.

### The library around it

#### The structure

The module `Mathlib.RingTheory.DividedPowers.Basic` defines `DividedPowers I` for an ideal `I : Ideal A` of a commutative semiring. Its field `DividedPowers.dpow` is a function `ℕ → A → A`. It is defined on all of $A$ for convenience and is zero outside $I$. For a structure `hI`, write $x^{[n]}$ for the value of `DividedPowers.dpow` at $n$ and $x$. The axioms are:

| Lean name | Statement |
|---|---|
| `DividedPowers.dpow_null` | $x^{[n]} = 0$ for $x \notin I$ |
| `DividedPowers.dpow_zero` | $x^{[0]} = 1$ for $x \in I$ |
| `DividedPowers.dpow_one` | $x^{[1]} = x$ for $x \in I$ |
| `DividedPowers.dpow_mem` | $x^{[n]} \in I$ for $x \in I$ and $n \ne 0$ |
| `DividedPowers.dpow_add` | $(x + y)^{[n]} = \sum_{i + j = n} x^{[i]}y^{[j]}$ |
| `DividedPowers.dpow_mul` | $(ax)^{[n]} = a^nx^{[n]}$ for $a \in A$ |
| `DividedPowers.mul_dpow` | $x^{[m]}x^{[n]} = \binom{m+n}{m}x^{[m+n]}$ |
| `DividedPowers.dpow_comp` | $(x^{[n]})^{[m]} = \frac{(mn)!}{m!(n!)^m}x^{[mn]}$ for $n \ne 0$ |

The coefficient in the last axiom is the integer `Nat.uniformBell m n`, the number of ways to split a set of $mn$ elements into $m$ blocks of size $n$. Over $\mathbb{Q}$ each axiom is an identity for $x^n/n!$.

The first consequence is `DividedPowers.factorial_mul_dpow_eq_pow`: $n!\,x^{[n]} = x^n$ for $x \in I$. So the divided powers are a choice of $x^n/n!$, and they are unique when the factorials are not zero divisors.

**Proof of `DividedPowers.factorial_mul_dpow_eq_pow`.** Use induction on $n$. For $n = 0$, both sides are $1$. Suppose $n!\,x^{[n]} = x^n$. By `DividedPowers.mul_dpow` with $m = 1$ and `DividedPowers.dpow_one`, $x \cdot x^{[n]} = (n + 1)x^{[n+1]}$. Multiply by $n!$: $x^{n+1} = x \cdot n!\,x^{[n]} = (n+1)!\,x^{[n+1]}$. $\square$

A divided power ideal is a nil ideal in many cases. The lemma `DividedPowers.nilpotent_of_mem_dpIdeal` says: if $n \ne 0$ and $n \cdot y = 0$ for all $y \in I$, then $x^n = 0$ for $x \in I$. The proof: $x^n = n!\,x^{[n]} = (n-1)! \cdot n\,x^{[n]}$, and $n\,x^{[n]} = 0$ since $x^{[n]} \in I$. In characteristic $p$ this gives $x^p = 0$ for all $x \in I$.

Other results of the module:

- `DividedPowers.dpow_sum` and `DividedPowers.dpow_add'` extend the sum axiom to finite sums and to elements outside the ideal.
- `DividedPowers.prod_dpow` is the multinomial form of `DividedPowers.mul_dpow`.
- `DividedPowers.exp` is the power series $\sum_n x^{[n]}T^n$, and `DividedPowers.exp_add` says that it turns sums into products.
- `DividedPowers.ext` says that two structures are equal when their `dpow` functions agree on $I$.
- `dividedPowersBot` is the unique structure on the zero ideal.

#### Examples

The module `Mathlib.RingTheory.DividedPowers.RatAlgebra` has the main examples. For an algebra $R$ over $\mathbb{Q}$, every ideal has the structure `DividedPowers.RatAlgebra.dividedPowers` with $x^{[n]} = (n!)^{-1}x^n$, `DividedPowers.RatAlgebra.dpow_apply`. It is the only one, `DividedPowers.RatAlgebra.dividedPowers_unique`: from `DividedPowers.factorial_mul_dpow_eq_pow`, the element $x^{[n]}$ is determined since $n!$ is a unit.

Without $\mathbb{Q}$ there are examples on nilpotent ideals:

- `DividedPowers.OfInvertibleFactorial.dividedPowers` works on an ideal $I$ with $I^n = 0$ when $(n - 1)!$ is a unit. It is $x^{[k]} = (k!)^{-1}x^k$ for $k < n$ and $0$ for $k \ge n$.
- `DividedPowers.OfSquareZero.dividedPowers` works on an ideal with $I^2 = 0$. It is $x^{[0]} = 1$, $x^{[1]} = x$ and $x^{[k]} = 0$ for $k \ge 2$, `DividedPowers.OfSquareZero.dpow_of_two_le`.
- `DividedPowers.CharP.dividedPowers` works for $A$ of prime characteristic $p$ and $I^p = 0$. Here $(p - 1)!$ is a unit.

**Proof sketch of `DividedPowers.OfSquareZero.dividedPowers`.** Check the axioms. All the products of two elements of $I$ are zero. For the sum axiom, $(x + y)^{[n]} = \sum_{i + j = n} x^{[i]}y^{[j]}$ holds for $n \le 1$ directly. For $n \ge 2$, every term on the right has $i \ge 2$, $j \ge 2$, or $i = j = 1$, so every term is $0$ or $xy = 0$. For `DividedPowers.mul_dpow`, both sides vanish unless $m + n \le 1$. For `DividedPowers.dpow_comp`, $(x^{[n]})^{[m]}$ with $n \ge 1$ is $0$ unless $m \le 1$ or $n = 1$, and the formula checks in each case. $\square$

The module `Mathlib.RingTheory.DividedPowers.Padic` has `PadicInt.dividedPowers`: the ideal $(p)$ of the $p$-adic integers $\mathbb{Z}_p$ has divided powers, with $x^{[n]} = x^n/n!$ computed in $\mathbb{Q}_p$, `PadicInt.coe_dpow_eq`. The point is that $v_p(n!) \le (n - 1)/(p - 1) < n$, so $x^n/n!$ is in $p\mathbb{Z}_p$ for $x \in p\mathbb{Z}_p$ and $n \ge 1$. The construction uses `DividedPowers.ofInjective`, which pulls back a divided power structure along an injective ring map.

#### Morphisms

The module `Mathlib.RingTheory.DividedPowers.DPMorphism` treats maps. For divided power ideals $(I, \gamma)$ of $A$ and $(J, \delta)$ of $B$, a ring map $f : A \to B$ is a divided power morphism, `DividedPowers.IsDPMorphism`, when $f(I) \subseteq J$ and $f(\gamma_n(x)) = \delta_n(f(x))$ for $x \in I$. The bundled form is the structure `DividedPowers.DPMorphism`, with `DividedPowers.DPMorphism.id` and `DividedPowers.DPMorphism.comp`.

It is enough to check the condition on generators. This is `DividedPowers.IsDPMorphism.on_span`: if $I$ is generated by a set $S$, $f(s) \in J$ for $s \in S$, and $f(\gamma_n(s)) = \delta_n(f(s))$ for all $s \in S$ and all $n$, then $f$ is a divided power morphism. The bundled version is `DividedPowers.DPMorphism.fromGens`.

**Proof sketch of `DividedPowers.IsDPMorphism.on_span`.** The set of $x \in I$ with $f(\gamma_n(x)) = \delta_n(f(x))$ for all $n$ contains $S$. It is closed under addition by the sum axiom: $f(\gamma_n(x + y)) = \sum_{i + j = n} f(\gamma_i(x))f(\gamma_j(y)) = \sum_{i + j = n} \delta_i(f(x))\delta_j(f(y)) = \delta_n(f(x + y))$. It is closed under multiplication by $a \in A$ by `DividedPowers.dpow_mul`: $f(\gamma_n(ax)) = f(a)^nf(\gamma_n(x)) = f(a)^n\delta_n(f(x)) = \delta_n(f(ax))$. So it is an ideal that contains $S$, and it is $I$. $\square$

#### Sub divided power ideals and quotients

The module `Mathlib.RingTheory.DividedPowers.SubDPIdeal` treats ideals that are stable under the divided powers. An ideal $J$ is a sub divided power ideal, `DividedPowers.IsSubDPIdeal`, when $J \le I$ and $\gamma_n(J) \subseteq J$ for $n \ne 0$. The bundled form `DividedPowers.SubDPIdeal` is a complete lattice, `DividedPowers.SubDPIdeal.instCompleteLattice`. Sums and intersections of sub divided power ideals are sub divided power ideals, `DividedPowers.isSubDPIdeal_sup`, `DividedPowers.isSubDPIdeal_iSup` and `DividedPowers.isSubDPIdeal_iInf`. An ideal generated by a set $S \subseteq I$ is a sub divided power ideal if and only if $\gamma_n(s) \in J$ for $s \in S$ and $n \ne 0$, `DividedPowers.span_isSubDPIdeal_iff`. The kernel of a divided power morphism meets $I$ in a sub divided power ideal, `DividedPowers.isSubDPIdeal_ker`.

The main use is quotients. If $J$ is an ideal of $A$ and $J \cap I$ is a sub divided power ideal of $I$, then the image of $I$ in $A/J$ has a unique divided power structure for which $A \to A/J$ is a divided power morphism. This is `DividedPowers.Quotient.dividedPowers`, with `DividedPowers.Quotient.isDPMorphism` and `DividedPowers.Quotient.dividedPowers_unique`. The form for any surjective ring map is `DividedPowers.Quotient.OfSurjective.dividedPowers`.

The ideal `DividedPowers.dpEqualizer` of two structures holds the elements of $I$ on which two divided power structures agree. It is a sub divided power ideal for both, and `DividedPowers.le_equalizer_of_isDPMorphism` compares it with the image of a morphism.

#### The divided power algebra

The module `Mathlib.RingTheory.DividedPowerAlgebra.Init` builds the divided power algebra $\Gamma_R(M)$ of an $R$-module $M$. The type `DividedPowerAlgebra R M` is the quotient of the polynomial ring `MvPolynomial (ℕ × M) R` by the relations `DividedPowerAlgebra.Rel`, which state the divided power axioms for the variables. The class of the variable $(n, m)$ is `DividedPowerAlgebra.dp R n m`, the $n$-th divided power of $m$.

| Lean name | Statement |
|---|---|
| `DividedPowerAlgebra.dp_zero` | $\mathrm{dp}_0(m) = 1$ |
| `DividedPowerAlgebra.dp_add` | $\mathrm{dp}_n(x + y) = \sum_{i + j = n} \mathrm{dp}_i(x)\,\mathrm{dp}_j(y)$ |
| `DividedPowerAlgebra.dp_mul` | $\mathrm{dp}_m(x)\,\mathrm{dp}_n(x) = \binom{m+n}{m}\mathrm{dp}_{m+n}(x)$ |
| `DividedPowerAlgebra.dp_smul` | $\mathrm{dp}_n(rx) = r^n\,\mathrm{dp}_n(x)$ |
| `DividedPowerAlgebra.natFactorial_mul_dp_eq` | $n!\,\mathrm{dp}_n(x) = \mathrm{dp}_1(x)^n$ |
| `DividedPowerAlgebra.embed` | the linear map $M \to \Gamma_R(M)$, $m \mapsto \mathrm{dp}_1(m)$ |
| `DividedPowerAlgebra.map` | the algebra map $\Gamma_R(M) \to \Gamma_R(N)$ from a linear map $M \to N$ |

The universal property is `DividedPowerAlgebra.lift`. Let $(I, \gamma)$ be a divided power ideal of an $R$-algebra $A$ and $g : M \to A$ a linear map with values in $I$. Then `DividedPowerAlgebra.lift` is the algebra map $\Gamma_R(M) \to A$ that sends $\mathrm{dp}_n(m)$ to $\gamma_n(g(m))$, `DividedPowerAlgebra.lift_apply_dp`. It is the only algebra map with this property, `DividedPowerAlgebra.lift_unique`, since the elements $\mathrm{dp}_n(m)$ generate $\Gamma_R(M)$. The functor laws for `DividedPowerAlgebra.map` are `DividedPowerAlgebra.map_id` and `DividedPowerAlgebra.map_comp`.

#### Common errors

1. The function `DividedPowers.dpow` is defined on all of $A$, and it is $0$ outside $I$, even for $n = 0$. So `DividedPowers.dpow_zero` needs the hypothesis $x \in I$.
2. `DividedPowers` is data, not a proposition. Two structures on the same ideal can differ, and a lemma about one structure says nothing about another. Over a $\mathbb{Q}$-algebra, use `DividedPowers.RatAlgebra.dividedPowers_unique` to identify them.
3. A quotient structure needs the condition on $J \cap I$, not on $J$. Prove `DividedPowers.IsSubDPIdeal` for the intersection before `DividedPowers.Quotient.dividedPowers` applies.

### Exercises

1. (A) Use `DividedPowers.factorial_mul_dpow_eq_pow` to show that $x^{[2]} \cdot 2 = x^2$, and compute $x^{[3]}$ in a $\mathbb{Q}$-algebra.
2. (A) Show that the ideal $(X)$ of $\mathbb{F}_p[X]/(X^p)$ has a divided power structure, with `DividedPowers.CharP.dividedPowers`.
3. (B) Show that the ideal $(2)$ of $\mathbb{Z}$ has no divided power structure. Hint: compute $2^{[3]}$ from `DividedPowers.factorial_mul_dpow_eq_pow` and check `DividedPowers.dpow_mem`.
4. (B) Check that $v_p(n!) < n$ for $n \ge 1$, and deduce that $x^n/n! \in p\mathbb{Z}_p$ for $x \in p\mathbb{Z}_p$, as in `PadicInt.dividedPowers`.
5. (B) Let $f : A \to B$ be a divided power morphism. Prove that $\ker f \cap I$ is a sub divided power ideal of $I$.
6. (C) Let $R = \mathbb{F}_p$ and $M = R$. Use `DividedPowerAlgebra.natFactorial_mul_dp_eq` to show that $\mathrm{dp}_1(1)^p = 0$ in $\Gamma_R(M)$, and deduce that the element $\mathrm{dp}_1(1)$ does not generate $\Gamma_R(M)$ as an $R$-algebra.

### Reference

<?reference?>
