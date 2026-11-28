---
title: Constructions and conversions of finitely supported functions
kind: api
modules:
  - Mathlib.Data.Finsupp.Notation
  - Mathlib.Data.Finsupp.Ext
  - Mathlib.Data.Finsupp.SMulWithZero
  - Mathlib.Data.Finsupp.SMul
  - Mathlib.Data.Finsupp.Pointwise
  - Mathlib.Data.Finsupp.Indicator
  - Mathlib.Data.Finsupp.BigOperators
  - Mathlib.Data.Finsupp.Fin
  - Mathlib.Data.Finsupp.Option
  - Mathlib.Data.Finsupp.Sigma
  - Mathlib.Data.Finsupp.Quotient
  - Mathlib.Data.Finsupp.AList
  - Mathlib.Data.Finsupp.ToDFinsupp
  - Mathlib.Data.Finsupp.Fintype
  - Mathlib.Data.Finsupp.Encodable
explains:
  E2: [Finsupp.addHom_ext, Finsupp.smul_apply, Finsupp.comapSMul_apply, Finsupp.support_mul, Finsupp.cons_tail, Finsupp.optionEquiv, Finset.support_sum_eq, Fintype.card_finsupp, finsuppEquivDFinsupp]
  E1: auto
families: []
requires: [V03.C02, V03.C03, V03.C04, V03.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Constructions and conversions of finitely supported functions

### Overview

The first two sections of this chapter give the type `α →₀ M`, the singles, the sums over the support and the maps of the domain. Around this core the library has many small modules. Each one adds one structure or one construction: a notation for explicit functions, the rule that an additive map is fixed by its values on singles, the scalar multiplication and the module structure, the pointwise product, the functions on a finset, the functions on `Fin (n + 1)`, on `Option α` and on a sigma type, the functions on a quotient, the conversions to association lists and to dependent functions, and the count of the functions when both types are finite.

This section goes through these modules in that order. The module structure `Finsupp.module` is the one that makes `α →₀ R` the free $R$-module on $\alpha$, the base of the volume on linear algebra. The other constructions are tools for induction on the domain and for moving between the forms of the same data.

### The library around it

#### Notation and extensionality

The module `Mathlib.Data.Finsupp.Notation` gives the notation `fun₀ | a => b | c => d` for the function with value $b$ at $a$, $d$ at $c$ and $0$ elsewhere. The single `Finsupp.single a b` is printed as `fun₀ | a => b`, so this form appears in the goals and in the statements of many lemmas. Updates are printed in the same way. The instance `Finsupp.instRepr` prints a function with a computable support in this notation.

The module `Mathlib.Data.Finsupp.Ext` gives the rule of extensionality for additive maps. Each $f : \alpha \to_0 M$ is a finite sum of singles, so an additive map out of `α →₀ M` is fixed by its values on singles:

$$\big(\forall x\, y,\ \varphi(\operatorname{single}(x, y)) = \psi(\operatorname{single}(x, y))\big) \implies \varphi = \psi.$$

This is `Finsupp.addHom_ext`. Its proof is the induction principle of Section 1: both maps send $0$ to $0$, and if they agree on $f$ and on a single, they agree on the sum. The form `Finsupp.addHom_ext'` compares the maps after `Finsupp.singleAddHom x` for each $x$, and the `ext` tactic uses it. The rules `Finsupp.mulHom_ext` and `Finsupp.mulHom_ext'` are the same for maps out of `Multiplicative (α →₀ M)`. The same fact in the language of submonoids is `Finsupp.add_closure_setOfPred_eq_single`: the singles generate `α →₀ M` as an additive monoid.

#### Scalar multiplication

If $R$ acts on $M$ and $c \cdot 0 = 0$, then $R$ acts on `α →₀ M` point by point. The module `Mathlib.Data.Finsupp.SMulWithZero` gives this action, `Finsupp.smulZeroClass`, with the rule `Finsupp.smul_apply`: $(c \cdot v)(a) = c \cdot v(a)$. Since $c \cdot 0 = 0$, the product has support inside the support of $v$, by `Finsupp.support_smul`. The rule `Finsupp.smul_single` gives $c \cdot \operatorname{single}(a, b) = \operatorname{single}(a, c \cdot b)$. The instances `Finsupp.isScalarTower`, `Finsupp.smulCommClass` and `Finsupp.isCentralScalar` carry the usual compatibilities from $M$.

The module `Mathlib.Data.Finsupp.SMul` adds the full structures: `Finsupp.distribMulAction` and `Finsupp.module`. So `α →₀ M` is an $R$-module when $M$ is. The main rules are these.

| Lean name | Statement |
|---|---|
| `Finsupp.sum_smul_index` | $(b \cdot g).\mathrm{sum}(h) = g.\mathrm{sum}(\lambda i\, a.\ h(i, b a))$ when $h(i, 0) = 0$ |
| `Finsupp.sum_smul_index'` | the same for an action $R$ on $M$ |
| `Finsupp.mapDomain_smul` | $\varphi_*(b \cdot v) = b \cdot \varphi_*(v)$ |
| `Finsupp.support_smul_eq` | $\operatorname{supp}(b \cdot g) = \operatorname{supp} g$ for $b \ne 0$ in a domain acting without torsion |
| `Finsupp.smul_single_one` | $b \cdot \operatorname{single}(a, 1) = \operatorname{single}(a, b)$ |
| `Finsupp.distribMulActionHom_ext` | an equivariant additive map is fixed by its values on singles |

The instances `Finsupp.faithfulSMul` and `Finsupp.moduleIsTorsionFree` say that the action stays faithful and torsion free, and `IsSMulRegular.finsupp` does the same for one regular scalar.

A second action moves the points instead of the values. If a monoid $G$ acts on $\alpha$, then `Finsupp.comapSMul` lets $G$ act on `α →₀ M` by $g \cdot \operatorname{single}(a, b) = \operatorname{single}(g \cdot a, b)$ (`Finsupp.comapSMul_single`). For a group, `Finsupp.comapSMul_apply` gives the value: $(g \cdot f)(a) = f(g^{-1} \cdot a)$. The inverse appears because the value at $a$ comes from the point that $g$ sends to $a$. This action is not an instance, since it would clash with the first one when $G = R$. The definitions `Finsupp.comapMulAction` and `Finsupp.comapDistribMulAction` give it as a structure to install by hand.

#### The pointwise product

The module `Mathlib.Data.Finsupp.Pointwise` gives the product of two functions point by point, with `Finsupp.mul_apply`: $(g_1 g_2)(a) = g_1(a) g_2(a)$. A value is nonzero only when both factors are nonzero, so `Finsupp.support_mul` gives $\operatorname{supp}(g_1 g_2) \subseteq \operatorname{supp} g_1 \cap \operatorname{supp} g_2$. There is no unit when $\alpha$ is infinite: the constant function $1$ does not have finite support. So the structures are the non unital ones: `Finsupp.instNonUnitalSemiring`, `Finsupp.instNonUnitalCommRing` and their relatives. This product is not the product of polynomials, which is a convolution and lives on the type `AddMonoidAlgebra`. The module also lets each function $\alpha \to \beta$ act on `α →₀ β` by pointwise multiplication (`Finsupp.pointwiseModule`).

#### Functions on a finset

For a finset $s$ and a function $f$ defined only at the points of $s$, `Finsupp.indicator s f` is the function equal to $f$ on $s$ and to $0$ outside. The rules are `Finsupp.indicator_apply`, `Finsupp.indicator_of_mem`, `Finsupp.indicator_of_notMem` and `Finsupp.support_indicator_subset`. The map $f \mapsto \operatorname{indicator}(s, f)$ is injective (`Finsupp.indicator_injective`), and for a function defined everywhere it is the indicator function of sets of Chapter 1 (`Finsupp.indicator_eq_set_indicator`).

The module `Mathlib.Data.Finsupp.BigOperators` controls the support of a sum of functions. The support of a sum lies in the union of the supports, and the two are equal when the supports are pairwise disjoint:

$$\operatorname{supp}\Big(\sum_{f \in s} f\Big) \subseteq \bigcup_{f \in s} \operatorname{supp} f, \qquad \text{with equality if the supports are pairwise disjoint.}$$

These are `Finset.support_sum_subset` and `Finset.support_sum_eq`, with the same rules for lists (`List.support_sum_eq`) and multisets (`Multiset.support_sum_eq`). For the equality: at a point $a$ of one support, all other functions of $s$ vanish, so the sum at $a$ is the value of one function, and it is not zero.

#### Changing the domain: Fin, Option and sigma types

Three modules split a function on a composite domain into simpler parts, for proofs by induction on the domain.

On `Fin (n + 1)`, `Finsupp.cons y s` puts $y$ at $0$ and shifts $s : \operatorname{Fin} n \to_0 M$ by one place, and `Finsupp.tail` removes the value at $0$. These are the forms of `Fin.cons` and `Fin.tail` for finitely supported functions. The rules `Finsupp.cons_zero`, `Finsupp.cons_succ`, `Finsupp.tail_cons` and `Finsupp.cons_tail` (that is, $\operatorname{cons}(t(0), \operatorname{tail} t) = t$) make a bijection between `Fin (n + 1) →₀ M` and `M × (Fin n →₀ M)`. The rule `Finsupp.cons_ne_zero_iff` says that $\operatorname{cons}(y, s) \ne 0$ if and only if $y \ne 0$ or $s \ne 0$.

On `Option α`, the same splitting takes the value at `none` and the rest. The functions are `Finsupp.optionElim y f` (value $y$ at `none`, $f(a)$ at `some a`) and `Finsupp.some f` (the restriction to the points `some a`). The equivalence `Finsupp.optionEquiv` packs them as `(Option α →₀ M) ≃ M × (α →₀ M)`. The sum rule `Finsupp.sum_option_index` splits a sum over the support into the term at `none` and the sum over the restriction.

On a sigma type $\Sigma k,\ \iota_k$, the function `Finsupp.embSigma` extends a function on one fibre $\iota_k$ by $0$ on the other fibres. The rules `Finsupp.embSigma_apply_self`, `Finsupp.embSigma_apply_of_ne` and `Finsupp.support_embSigma` give its values and its support, and `Finsupp.split_embSigma_self` says that the map `Finsupp.split` recovers the original function.

#### Quotients and association lists

Let $r$ be a relation on $\alpha$ and let $f : \alpha \to_0 \beta$ be constant on the classes of $r$. Then `Quot.liftFinsupp f h` is the induced function on the quotient, with `Quot.liftFinsupp_mk` as its rule, and `Quotient.liftFinsupp` is the same for a setoid. The support stays finite, because the classes in the support are images of points of the finite support of $f$. When each class is finite, `Setoid.liftFinsuppEquiv` is a bijection between the functions on $\alpha$ that are constant on classes and the finitely supported functions on the quotient.

An association list `AList` is a list of pairs with no repeated key. The function `AList.lookupFinsupp` reads a list as a finitely supported function, with the value $0$ at a missing key (`AList.lookupFinsupp_apply`), and `Finsupp.toAList` goes back. The rule `Finsupp.toAList_lookupFinsupp` says that the round trip gives the original function, so `AList.lookupFinsupp` is surjective (`AList.lookupFinsupp_surjective`). The other round trip is not the identity, because a list can hold the value $0$ at a key.

#### Dependent functions

The type `Π₀ i, β i` of dependent functions with finite support is the subject of the section on `DFinsupp`. When all the types $\beta_i$ are the same type $M$, the two types hold the same data. The module `Mathlib.Data.Finsupp.ToDFinsupp` gives the two maps `Finsupp.toDFinsupp` and `DFinsupp.toFinsupp`, with the rules `Finsupp.toDFinsupp_coe` (the function does not change) and `Finsupp.toDFinsupp_single`. The maps respect addition, negation, subtraction and scalar multiplication, and the module bundles them as `finsuppEquivDFinsupp` (an equivalence of types), `finsuppAddEquivDFinsupp` (an additive equivalence) and `finsuppLequivDFinsupp` (a linear equivalence). The map `DFinsupp.toFinsupp` needs decidable equality on the points and the decidability of $m \ne 0$, because it computes the support. A second family identifies functions on a sigma type with dependent functions of functions: `sigmaFinsuppEquivDFinsupp` and `sigmaFinsuppLequivDFinsupp` give `((i : ι) × η i →₀ N) ≃ Π₀ i, (η i →₀ N)`.

#### Finiteness and countability

If $\iota$ and $\alpha$ are finite, then `α →₀ M` has the instance `Finsupp.fintype`, and

$$\#(\iota \to_0 \alpha) = (\#\alpha)^{\#\iota}.$$

This is `Fintype.card_finsupp`. The proof: on a finite type each function has finite support, so `ι →₀ α` is in bijection with all functions `ι → α`, and the count of Chapter 4 applies. If $\iota$ is infinite and $\alpha$ has two elements, the type is infinite (`Finsupp.infinite_of_left`), because the singles at distinct points are distinct. The module `Mathlib.Data.Finsupp.Encodable` gives `instCountableFinsupp`: the type is countable when $\alpha$ and $\beta$ are countable, and `instEncodableFinsuppOfDecidableNeOfNat` gives an explicit code.

#### Common errors

1. A learner expects `Finsupp.single a 2 * Finsupp.single b 3` to be the product of polynomials, that is $6\,\operatorname{single}(a + b, 1)$. The product on `α →₀ R` is pointwise, and it is $0$ for $a \ne b$. The product of polynomials is the product of `AddMonoidAlgebra`.
2. A learner writes `g • f` with $g$ in a group acting on the points, and Lean uses the action on the values. The action on the points is `Finsupp.comapSMul`, and it is not an instance. Install it with `Finsupp.comapMulAction` in a local instance.
3. A learner uses `DFinsupp.toFinsupp` and gets a goal about `Decidable`. The map needs `DecidableEq ι` and a decision of $m \ne 0$. Use `classical`, or use `Finsupp.toDFinsupp` in the other direction, which needs nothing.

### Exercises

1. (A) Compute `Finsupp.optionEquiv` of the function `fun₀ | none => 3 | some 2 => 5` in `Option ℕ →₀ ℕ`.
2. (A) Show that $2 \cdot (\operatorname{single}(1, 3) + \operatorname{single}(4, -1)) = \operatorname{single}(1, 6) + \operatorname{single}(4, -2)$ with `Finsupp.smul_single`.
3. (A) Use `Fintype.card_finsupp` to count the functions `Fin 3 →₀ Fin 4`, and compare with the count of all functions.
4. (B) Show with `Finsupp.addHom_ext` that two additive maps $\varphi, \psi : (\alpha \to_0 \mathbb{Z}) \to \mathbb{Z}$ agree when $\varphi(\operatorname{single}(a, 1)) = \psi(\operatorname{single}(a, 1))$ for all $a$.
5. (B) Give a finset $s$ of functions in `ℕ →₀ ℤ` such that the inclusion of `Finset.support_sum_subset` is strict. Show that no such finset exists in `ℕ →₀ ℕ`.
6. (C) Prove `Setoid.liftFinsuppEquiv` for the relation of congruence modulo $2$ on `Fin 6`: describe both sides and the bijection.

### Reference

<?reference?>
