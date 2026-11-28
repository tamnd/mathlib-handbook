---
title: Dependent functions with finite support
kind: api
modules:
  - Mathlib.Data.DFinsupp.Defs
  - Mathlib.Data.DFinsupp.Ext
  - Mathlib.Data.DFinsupp.Notation
  - Mathlib.Data.DFinsupp.BigOperators
  - Mathlib.Data.DFinsupp.Module
  - Mathlib.Data.DFinsupp.Submonoid
  - Mathlib.Data.DFinsupp.Sigma
  - Mathlib.Data.DFinsupp.Encodable
  - Mathlib.Data.DFinsupp.Small
  - Mathlib.Data.DFinsupp.FiniteInfinite
explains:
  E2: [DFinsupp.ext, DFinsupp.induction, DFinsupp.update_eq_erase_add_single, DFinsupp.sum_add_index, DFinsupp.sumAddHom_single, DFinsupp.addHom_ext, DFinsupp.sigmaCurryEquiv, AddSubmonoid.mem_iSup_iff_exists_dfinsupp, DFinsupp.infinite_of_exists_right]
  E1: auto
families: []
requires: [V03.C03, V03.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Dependent functions with finite support

### Overview

A finitely supported function $f : X \to_0 M$ takes all its values in one type $M$. Some constructions need a different target at each point. A direct sum $\bigoplus_i M_i$ of modules is the set of families $(m_i)_i$ with $m_i \in M_i$ and only finitely many $m_i \neq 0$. The library calls such a family a *dependent function with finite support*. The type is `DFinsupp β` for a family of types $\beta : \iota \to \mathrm{Type}$, each with a zero, and the notation is $\Pi_0\, i,\ \beta\, i$. The direct sum `DirectSum` of Volume 6 is defined as this type.

The interface follows the interface of `Finsupp`: a value at each point, a finite support, single functions, sums over the support and an induction principle. Two differences matter in practice. First, the support needs decidability. Second, the target of the value at $i$ depends on $i$, so a statement such as $f\,i = g\,j$ does not type check when $i$ and $j$ are different variables. This section lists the API in the modules `Mathlib.Data.DFinsupp.Defs` to `Mathlib.Data.DFinsupp.FiniteInfinite`. The next section treats the order on the type.

### The library around it

#### The type and its support

A term of $\Pi_0\, i,\ \beta\, i$ is a structure with two fields. The field `DFinsupp.toFun` is the function $\prod_i \beta\, i$. The field `DFinsupp.support'` is a truncated multiset $s$ with $i \in s$ or $f\,i = 0$ for each $i$. So the structure does not store the support. It stores a finite set that contains the support, and the truncation hides which one. Because of this design the constructions are computable, and the type has decidable equality (`DFinsupp.instDecidableEq`) when $\iota$ and each $\beta\, i$ have decidable equality.

The cost is that `DFinsupp.support` needs instances. Its signature asks for `DecidableEq ι` and for a decision of $x \neq 0$ in each $\beta\, i$. The support is then the finite set of $i$ in the stored multiset with $f\,i \neq 0$, and `DFinsupp.mem_support_iff` states $i \in \mathrm{supp}\, f \leftrightarrow f\,i \neq 0$. A `Finsupp`, by contrast, stores its support as a field and is noncomputable.

The coercion to functions makes $f\,i$ meaningful, and `DFinsupp.ext` is the extensionality lemma: if $f\,i = g\,i$ for each $i$, then $f = g$. The tactic *ext* uses it. The pointwise operations come from `DFinsupp.zipWith`, and the simp lemmas `DFinsupp.zero_apply`, `DFinsupp.add_apply` and `DFinsupp.coe_add` give their values. The instances `DFinsupp.addCommMonoid` and `DFinsupp.addCommGroup` give the algebraic structure, and `DFinsupp.support_add` gives $\mathrm{supp}(f + g) \subseteq \mathrm{supp}\, f \cup \mathrm{supp}\, g$.

#### Constructions

The module `Mathlib.Data.DFinsupp.Defs` gives the basic constructions.

| Lean name | Meaning |
|---|---|
| `DFinsupp.single` | the function with value $b$ at $i$ and $0$ elsewhere |
| `DFinsupp.mk` | the function from a finite set $s$ and a value at each point of $s$ |
| `DFinsupp.update` | the function $f$ with its value at $i$ changed to $b$ |
| `DFinsupp.erase` | the function $f$ with its value at $i$ changed to $0$ |
| `DFinsupp.mapRange` | the function $i \mapsto g_i(f\,i)$, for maps $g_i$ with $g_i(0) = 0$ |
| `DFinsupp.zipWith` | the function $i \mapsto g_i(f\,i, f'\,i)$, for maps with $g_i(0, 0) = 0$ |
| `DFinsupp.filter` | the function $f$ with the values outside a predicate $p$ set to $0$ |
| `DFinsupp.subtypeDomain` | the restriction of $f$ to the points that satisfy $p$ |
| `DFinsupp.comapDomain` | the composite $f \circ h$, for an injective map $h$ |
| `DFinsupp.equivFunOnFintype` | the equivalence with all functions, for a finite index type |

The module `Mathlib.Data.DFinsupp.Notation` gives the notation $\mathtt{fun_0} \mid i \Rightarrow b$ for `DFinsupp.single i b`. The same notation also stands for `Finsupp.single`, and the expected type selects the meaning. A longer form $\mathtt{fun_0} \mid i \Rightarrow b \mid j \Rightarrow c$ unfolds to `DFinsupp.update` of a single function. The pretty printer shows single functions in this notation, so goals often contain it.

The values of a single function come from `DFinsupp.single_eq_same` and `DFinsupp.single_eq_of_ne`. Both state the value at one point, $(\mathtt{fun_0} \mid i \Rightarrow b)\, i = b$ and the value $0$ at $i' \neq i$. The general lemma `DFinsupp.single_apply` has a dependent if-then-else, because $b : \beta\, i$ must be cast to $\beta\, i'$ when $i = i'$. In proofs the two special lemmas are easier to use. Similarly `DFinsupp.erase_apply` gives the value of an erased function, and `DFinsupp.update_eq_erase_add_single` writes an update as an erase and a single:
$$f[i \mapsto b] = \mathrm{erase}_i\, f + (\mathtt{fun_0} \mid i \Rightarrow b).$$

#### Induction and homomorphisms

The lemma `DFinsupp.induction` proves a property $p$ of each $f$ from two cases: $p\,0$, and $p\,f \to p((\mathtt{fun_0} \mid i \Rightarrow b) + f)$ when $f\,i = 0$ and $b \neq 0$. The variant `DFinsupp.induction₂` adds the single function on the right. The use is with the tactic *induction f using DFinsupp.induction*.

For additive maps the library gives extensionality lemmas that avoid induction. The lemma `DFinsupp.addHom_ext` says that two additive monoid homomorphisms out of $\Pi_0\, i,\ \beta\, i$ are equal if they agree on each single function. The primed form `DFinsupp.addHom_ext'` asks for equality of the composites with `DFinsupp.singleAddHom` for each $i$, and the tactic *ext* uses it. The reason behind both is `DFinsupp.add_closure_iUnion_range_single`: the single functions generate the whole additive monoid.

#### Sums over the support

Let $f : \Pi_0\, i,\ \beta\, i$ and let $g\,i : \beta\, i \to \gamma$ for a commutative monoid $\gamma$. The sum `DFinsupp.sum f g` is $\sum_{i \in \mathrm{supp}\, f} g\,i\,(f\,i)$, and `DFinsupp.prod` is the product. The definitions follow `Finsupp.sum` from the previous section. The main lemmas are these.

| Lean name | Statement |
|---|---|
| `DFinsupp.sum_zero_index` | the sum over $0$ is $0$ |
| `DFinsupp.sum_single_index` | the sum over a single function is $g\,i\,b$, if $g\,i\,0 = 0$ |
| `DFinsupp.sum_add_index` | $(f + f').\mathrm{sum}\, g = f.\mathrm{sum}\, g + f'.\mathrm{sum}\, g$, if each $g\,i$ is additive |
| `DFinsupp.sum_sub_index` | the same for a difference, if each $g\,i$ respects subtraction |
| `DFinsupp.sum_eq_sum_fintype` | for a finite index type, the sum over all $i$ |
| `DFinsupp.finsetSum_apply` | the value of a finite sum of functions is the sum of the values |
| `DFinsupp.sum_comm` | two sums over two functions commute |

The bundled form is `DFinsupp.sumAddHom`. For a family $\varphi_i : \beta\, i \to^+ \gamma$ of additive homomorphisms it gives one homomorphism $\Pi_0\, i,\ \beta\, i \to^+ \gamma$. The lemma `DFinsupp.sumAddHom_single` gives its value on a single function, $\varphi_i\, x$, and `DFinsupp.sumAddHom_apply` rewrites it to `DFinsupp.sum`. The equivalence `DFinsupp.liftAddHom` states the universal property of the direct sum: families of homomorphisms correspond to homomorphisms out of $\Pi_0\, i,\ \beta\, i$. The lemma `DFinsupp.liftAddHom_apply_single` gives its value on a single function. Volume 6 builds the universal property of `DirectSum` on these maps.

#### Modules, submonoids and sigma types

When each $\beta\, i$ is a module over a semiring $R$, the instance `DFinsupp.module` makes $\Pi_0\, i,\ \beta\, i$ a module. Scalar multiplication is pointwise (`DFinsupp.smul_apply`, `DFinsupp.coe_smul`), and `DFinsupp.single_smul` moves a scalar into a single function. The module `Mathlib.Data.DFinsupp.Module` also gives linear forms of the constructions: `DFinsupp.coeFnLinearMap`, `DFinsupp.filterLinearMap` and `DFinsupp.subtypeDomainLinearMap`. The linear sum `DFinsupp.lsum` and the extensionality lemma `DFinsupp.lhom_ext` are in `Mathlib.LinearAlgebra.DFinsupp`.

The module `Mathlib.Data.DFinsupp.Submonoid` describes a supremum of submonoids. For a family $S_i$ of additive submonoids of a commutative monoid $\gamma$, the lemma `AddSubmonoid.mem_iSup_iff_exists_dfinsupp` says that $x \in \sup_i S_i$ if and only if $x$ is the sum of a dependent function $f$ with $f\,i \in S_i$. The lemma `AddSubmonoid.iSup_eq_mrange_dfinsuppSumAddHom` states the same as an equality with a range. The lemmas `dfinsuppSum_mem` and `dfinsuppSumAddHom_mem` say that a submonoid that contains each term contains the sum.

The module `Mathlib.Data.DFinsupp.Sigma` curries over a sigma type. A function on pairs $(i, j)$ with $j : \alpha\, i$ is the same as a function of $i$ whose values are functions of $j$. The map `DFinsupp.sigmaCurry` goes one way and `DFinsupp.sigmaUncurry` goes back. The equivalence `DFinsupp.sigmaCurryEquiv` combines them, and `DFinsupp.sigmaCurry_single` shows that a single function on a pair becomes a single function of single functions.

#### Size of the type

Three short modules state size results. The module `Mathlib.Data.DFinsupp.Encodable` gives an `Encodable` instance and a `Countable` instance. So the type is countable when $\iota$ and each $\beta\, i$ are countable. The module `Mathlib.Data.DFinsupp.Small` gives `DFinsupp.small`: if $\iota$ and each $\beta\, i$ are small in a universe, then so is the type. The module `Mathlib.Data.DFinsupp.FiniteInfinite` gives `DFinsupp.fintype` for finite $\iota$ and finite $\beta\, i$. In the other direction, `DFinsupp.infinite_of_left` makes the type infinite for an infinite index type with nontrivial values, and `DFinsupp.infinite_of_exists_right` makes it infinite when one $\beta\, i$ is infinite.

#### Common errors

1. `DFinsupp.support` and `DFinsupp.sum` ask for decidability of $x \neq 0$ in each $\beta\, i$. In a classical proof the instances can disagree with the instances in the statement of a lemma, and a rewrite then fails. The tactic *convert*, or *classical* at the start of the proof, solves most such cases.
2. `DFinsupp.single_apply` has a dependent if-then-else with a cast. A rewrite with it often leaves a goal that *simp* cannot close. Use `DFinsupp.single_eq_same` and `DFinsupp.single_eq_of_ne` after a case split on $i = i'$.
3. The notation $\mathtt{fun_0} \mid i \Rightarrow b$ elaborates to `Finsupp.single` by default. Without an expected type of the form $\Pi_0\, i,\ \beta\, i$, a term in this notation is a `Finsupp`.

### Exercises

1. (A) Prove that `DFinsupp.single i` is injective, with `DFinsupp.single_eq_same`.
2. (A) Prove that $\mathrm{supp}(\mathtt{fun_0} \mid i \Rightarrow b) = \{i\}$ when $b \neq 0$, with `Finset.ext` and `DFinsupp.mem_support_iff`.
3. (B) Show with `DFinsupp.induction` that each $f : \Pi_0\, i,\ \beta\, i$ is a finite sum of single functions, one for each point of its support.
4. (B) Let $\varphi$ and $\psi$ be two additive homomorphisms out of $\Pi_0\, i,\ \beta\, i$ that agree on each single function. Prove $\varphi = \psi$ with `DFinsupp.addHom_ext`, and then prove it again with `DFinsupp.induction` and `DFinsupp.sum_add_index`.
5. (B) Use `AddSubmonoid.mem_iSup_iff_exists_dfinsupp` to show that the supremum of the submonoids $n \mathbb{N}$ for $n \geq 2$ in $\mathbb{N}$ contains every natural number except $1$.
6. (C) Prove that $\Pi_0\, (n : \mathbb{N}),\ \mathbb{Z}$ is countable but not finite, with the instances of the modules `Mathlib.Data.DFinsupp.Encodable` and `Mathlib.Data.DFinsupp.FiniteInfinite`.

### Reference

<?reference?>
