---
title: Substitution of power series
kind: api
modules:
  - Mathlib.RingTheory.MvPowerSeries.Substitution
  - Mathlib.RingTheory.PowerSeries.Substitution
  - Mathlib.RingTheory.MvPowerSeries.LinearTopology
explains:
  E2: [MvPowerSeries.HasSubst, MvPowerSeries.subst, MvPowerSeries.substAlgHom, MvPowerSeries.coeff_subst, MvPowerSeries.subst_comp_subst, PowerSeries.subst, PowerSeries.substInv, PowerSeries.le_order_subst, MvPowerSeries.LinearTopology.hasBasis_nhds_zero]
  E1: auto
families: []
requires: [V06.C05, V09.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Substitution of power series

### Overview

A power series $g$ with constant coefficient $0$ can be substituted into any power series $f$: the composite $f(g) = \sum_n a_n g^n$ is again a power series, because $g^n$ has order at least $n$ and so each coefficient of the sum is a finite sum. For example, substitution of $g = X + X^2$ into $f = 1/(1 - X)$ gives $1/(1 - X - X^2)$, the generating function of the Fibonacci numbers. Substitution is the operation behind the composition of generating functions, the change of variables in formal groups, and the compositional inverse of a series $u X + \cdots$ with $u$ a unit.

The condition on $g$ can be weakened: it is enough that the constant coefficient of $g$ is nilpotent, since then the powers of $g$ still tend to $0$ in the product topology. In several variables a family of series $g_1, g_2, \ldots$ can be substituted for the variables $X_1, X_2, \ldots$ of $f$ when each constant coefficient is nilpotent and, for infinitely many variables, each monomial occurs in only finitely many $g_i$.

The library defines substitution as an evaluation in the sense of Section 5, for the discrete topology on the coefficients. This section is a guide to the two modules on substitution and to the module on the linear topology of power series rings, which makes the evaluation work over coefficient rings that are not discrete.

### The library around it

**Families that can be substituted.** The module `Mathlib.RingTheory.MvPowerSeries.Substitution` defines the structure `MvPowerSeries.HasSubst a` for a family $a : \sigma \to S[[\tau]]$. It has two fields: the constant coefficient of each $a_s$ is nilpotent, `MvPowerSeries.HasSubst.const_coeff`, and for each exponent $d$ only finitely many $a_s$ have a nonzero coefficient of $X^d$, `MvPowerSeries.HasSubst.coeff_zero`. For finitely many variables the second condition is automatic: `MvPowerSeries.hasSubst_of_constantCoeff_nilpotent` and `MvPowerSeries.hasSubst_of_constantCoeff_zero` give the property from the constant coefficients. The variables themselves can be substituted, `MvPowerSeries.HasSubst.X`, and so can their powers, `MvPowerSeries.HasSubst.X_pow`. The property is closed under sums, products by arbitrary series and scalar multiplication, `MvPowerSeries.HasSubst.add`, `MvPowerSeries.HasSubst.mul_left` and `MvPowerSeries.HasSubst.smul`, and these closure rules are packaged as an ideal, `MvPowerSeries.hasSubstIdeal`. For the discrete topology on $S$ it is the same as the condition of evaluation, `MvPowerSeries.hasSubst_iff_hasEval_of_discreteTopology`.

**The substitution map.** The function `MvPowerSeries.subst a f` substitutes $a_s$ for $X_s$ in $f$. It is defined for all $a$ by `MvPowerSeries.eval₂` with the discrete uniform structures on $R$ and $S$, `MvPowerSeries.subst_eq_eval₂`, so without `MvPowerSeries.HasSubst a` its value is meaningless. Under this hypothesis the bundled form `MvPowerSeries.substAlgHom ha` is an $R$-algebra map $R[[\sigma]] \to S[[\tau]]$, with `MvPowerSeries.coe_substAlgHom`. It sends $X_s$ to $a_s$, `MvPowerSeries.subst_X`, keeps constants, `MvPowerSeries.subst_C`, and is additive and multiplicative, `MvPowerSeries.subst_add` and `MvPowerSeries.subst_mul`. On a polynomial it is the evaluation of polynomials, `MvPowerSeries.substAlgHom_coe`. Each coefficient of the result is a finite sum:
$$\operatorname{coeff}_e(f(a)) = \sum_d \operatorname{coeff}_d(f) \operatorname{coeff}_e(a^d),$$
which is `MvPowerSeries.coeff_subst`, with the finiteness in `MvPowerSeries.coeff_subst_finite`. Substitution of the variables gives the map of coefficients, `MvPowerSeries.map_algebraMap_eq_subst_X`, and substitution of $c_s X_s$ is the rescaling `MvPowerSeries.rescale`, `MvPowerSeries.rescale_eq_subst`.

**Composition and order.** Substitutions compose: substitution of $a$ and then of $b$ is the substitution of the family $s \mapsto a_s(b)$,
$$f(a)(b) = f(a(b)),$$
which is `MvPowerSeries.subst_comp_subst`, with the condition `MvPowerSeries.HasSubst.comp` for the composite family. Substitution commutes with maps of coefficients, `MvPowerSeries.map_subst`, and with infinite sums, `MvPowerSeries.subst_tsum`. It is continuous for the product topologies, `MvPowerSeries.continuous_subst`. The order of the result is at least the product of the orders, `MvPowerSeries.le_order_subst`, with a weighted version `MvPowerSeries.le_weightedOrder_subst`. If $f$ and all the $a_s$ have constant coefficient $0$, then so does $f(a)$, `MvPowerSeries.constantCoeff_subst_eq_zero`. The constant coefficient of $f(a)$ in general is a finite sum, `MvPowerSeries.constantCoeff_subst`, because only finitely many monomials of $f$ contribute to it. The lemmas on `MvPowerSeries.truncTotal`, such as `MvPowerSeries.truncTotal_subst`, compute the truncation of $f(a)$ from truncations of $f$ and of the $a_s$.

**One variable.** The module `Mathlib.RingTheory.PowerSeries.Substitution` gives the forms for $R[[X]]$. Here `PowerSeries.HasSubst a` is an abbreviation for the nilpotence of the constant coefficient of $a$, `PowerSeries.hasSubst_iff`, and `PowerSeries.HasSubst.of_constantCoeff_zero'` gives it for a series in one variable with constant coefficient $0$. The substitution `PowerSeries.subst a f` puts $a$ in place of $X$, and `PowerSeries.substAlgHom` is its bundled form. The basic rules are `PowerSeries.subst_X`, `PowerSeries.coeff_subst`, `PowerSeries.subst_comp_subst` and `PowerSeries.le_order_subst`. For $a = X^k$ the coefficients are explicit, `PowerSeries.coeff_subst_X_pow`. Rescaling is a substitution, `PowerSeries.rescale_eq_subst`, and a substitution by a series of degree $1$ commutes with it, `PowerSeries.subst_rescale_of_degree_eq_one`.

**Compositional inverses.** Let $P = u X + O(X^2)$ with $u$ invertible. The series `PowerSeries.substInv P` is its inverse for composition. Its constant coefficient is $0$, `PowerSeries.constantCoeff_substInv`, its linear coefficient is $u^{-1}$, `PowerSeries.coeff_one_substInv`, and substitution of either series into the other gives $X$, `PowerSeries.subst_substInv_left` and `PowerSeries.subst_substInv_right`. The variant `PowerSeries.substInvOfIsUnit` takes a proof that $u$ is a unit in place of an `Invertible` instance, with `PowerSeries.subst_substInvOfIsUnit_left` and `PowerSeries.subst_substInvOfIsUnit_right`. The proof constructs the coefficients of the inverse by recursion, in the auxiliary function `PowerSeries.substInvFun`. With these inverses the series of the form $X + O(X^2)$ form a group under substitution, and the series $u X + O(X^2)$ with $u$ a unit form a larger group.

**Linear topology.** The module `Mathlib.RingTheory.MvPowerSeries.LinearTopology` treats a ring $R$ whose topology is linear, that is, $0$ has a basis of neighborhoods made of ideals. For a two-sided ideal $J$ of $R$ and an exponent $d$, the set `MvPowerSeries.LinearTopology.basis σ R (J, d)` is the ideal of the series whose coefficients of exponent at most $d$ lie in $J$. These ideals form a basis of neighborhoods of $0$ for the product topology, `MvPowerSeries.LinearTopology.hasBasis_nhds_zero`, so the product topology on $R[[\sigma]]$ is linear again, by the instance `MvPowerSeries.LinearTopology.instIsLinearTopologyOfMulOpposite`. A series is topologically nilpotent exactly when its constant coefficient is, `MvPowerSeries.LinearTopology.isTopologicallyNilpotent_iff_constantCoeff`. These facts give the condition `MvPowerSeries.HasEval` of Section 5 for series in a ring of power series.

#### Common errors

1. `MvPowerSeries.subst a f` and `PowerSeries.subst a f` are total functions. Without the condition `MvPowerSeries.HasSubst a` or `PowerSeries.HasSubst a` their value is junk, and almost every lemma takes the condition as a hypothesis. Prove it first, usually with `PowerSeries.HasSubst.of_constantCoeff_zero'` or `MvPowerSeries.hasSubst_of_constantCoeff_zero`.
2. In `PowerSeries.subst a f` the first argument is the series that is substituted and the second is the series that receives it, so `PowerSeries.subst a f` is $f(a)$. Dot notation can put a series in either position, so read the elaborated term before rewriting with a lemma such as `PowerSeries.subst_substInv_left`.
3. The result of `PowerSeries.subst a f` lives in the ring of $a$, which can be a ring of power series in several variables. A goal stated in `PowerSeries S` may need `PowerSeries.subst` with $a$ of type `PowerSeries S`, and a cast between `PowerSeries S` and `MvPowerSeries Unit S` can appear.

### Exercises

1. (A) Compute the coefficients of $X^0, \ldots, X^4$ in the substitution of $X + X^2$ into $\sum_n X^n$, and recognize the Fibonacci numbers.
2. (A) Use `PowerSeries.coeff_subst_X_pow` to describe the coefficients of $f(X^2)$ in terms of those of $f$.
3. (B) Prove that `PowerSeries.HasSubst (1 + X)` fails over $\mathbb{Z}$, and that it holds over $\mathbb{Z}/4$ for the series $2 + X$.
4. (B) Compute the first four coefficients of `PowerSeries.substInv` of $P = X + X^2$ over $\mathbb{Q}$, and check the result with `PowerSeries.subst_substInv_left`.
5. (B) Use `MvPowerSeries.subst_comp_subst` to prove that rescaling by $a$ and then by $b$ is rescaling by $a b$.
6. (C) Let $f, g \in R[[X]]$ have constant coefficient $0$ and linear coefficient $1$. Prove that the series with these properties form a group under substitution, using `PowerSeries.subst_comp_subst` and `PowerSeries.substInv`.

### Reference

<?reference?>
