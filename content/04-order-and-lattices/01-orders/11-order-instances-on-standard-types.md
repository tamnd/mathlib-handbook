---
title: Order instances on standard types
kind: api
modules:
  - Mathlib.Order.ULift
  - Mathlib.Order.Shrink
  - Mathlib.Order.PropInstances
  - Mathlib.Order.Std
  - Mathlib.Order.Preorder.Finsupp
  - Mathlib.Order.Sym2
  - Mathlib.Order.Quotient
  - Mathlib.Order.Restriction
explains:
  E2: [Prop.isCompl_iff, orderIsoShrink, Finsupp.le_def, Finsupp.support_sup_union_support_inf, Sym2.inf_eq_inf_and_sup_eq_sup, Quotient.mk_le_mk, Quotient.lift_monotone, Preorder.restrictLe₂_comp_restrictLe]
  E1: auto
families: []
requires: [V01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Order instances on standard types

### Overview

The first section of this chapter builds new orders from old ones: the product, the lexicographic order and the order pulled back along a function. Mathlib has many more such constructions, one for each standard type former. This section collects the small ones. A lifted type in a higher universe, a small model of a type, the propositions, the finitely supported functions, the unordered pairs, the quotients of an order and the restrictions of a function to an initial interval each get an order or a lattice. The modules are short, and most of their lemmas say that a canonical map keeps the order.

A reader meets these instances often, but rarely by name. The instance on Prop makes `p ≤ q` mean $p \to q$, so a statement about sets or predicates can use the lattice lemmas. The instance on `ι →₀ M` makes the pointwise order available for polynomials and multisets. The quotient order turns a monotone function that is constant on classes into a monotone function on the quotient. The other modules matter mostly for the authors of new instances.

### The library around it

#### Lifts and small models

The module `Mathlib.Order.ULift` puts on `ULift α` each order structure of $\alpha$, from a bare relation $\le$ up to the Boolean algebra structure. The structure is transported along the equivalence between $\alpha$ and `ULift α`, with the maps up and down. The simp lemmas come in pairs: `ULift.up_le` says $\mathrm{up}(a) \le \mathrm{up}(b) \leftrightarrow a \le b$, and `ULift.down_le` says $\mathrm{down}(a) \le \mathrm{down}(b) \leftrightarrow a \le b$. The same pattern names `ULift.up_lt`, `ULift.down_lt`, `ULift.up_sup`, `ULift.down_sup`, `ULift.up_inf`, `ULift.down_inf`, `ULift.up_compl` and `ULift.down_compl`. The instances `ULift.instPreorder` and `ULift.instPartialOrder` are the base, and the docstring of the module says that the larger classes live next to the matching instances on products.

The module `Mathlib.Order.Shrink` does the same for `Shrink α`, the model of a type $\alpha$ in a smaller universe that exists when $\alpha$ is `Small`. The equivalence `equivShrink α` transports the order, and `orderIsoShrink α` bundles it as an order isomorphism $\alpha \simeq_o \mathrm{Shrink}\,\alpha$. The instances cover preorders, partial orders, linear orders, the bottom and top elements, the successor and predecessor orders, and well-foundedness: `instLinearOrderShrink`, `instOrderBotShrink`, `instSuccOrderShrink` and `instWellFoundedLTShrink`. The lemmas `equivShrink_le_equivShrink`, `equivShrink_lt_equivShrink`, `equivShrink_bot` and `equivShrink_top` say that the equivalence keeps each piece of structure. The proof of `orderIsoShrink` is one line: an equivalence that keeps $\le$ in both directions is an order isomorphism, and here $\le$ on the target is defined as $\le$ on the preimages.

#### The order on propositions

The module `Mathlib.Order.PropInstances` makes Prop a bounded distributive lattice and a linear order. The order is implication, as `le_Prop_eq` states. The other identities are the expected ones.

| Lean name | Statement |
|---|---|
| `Prop.bot_eq_false` | $\bot = \mathrm{False}$ |
| `Prop.top_eq_true` | $\top = \mathrm{True}$ |
| `sup_Prop_eq` | $p \sqcup q = p \lor q$ |
| `inf_Prop_eq` | $p \sqcap q = p \land q$ |
| `Prop.disjoint_iff` | `Disjoint p q` if and only if $\lnot(p \land q)$ |
| `Prop.codisjoint_iff` | `Codisjoint p q` if and only if $p \lor q$ |
| `Prop.isCompl_iff` | `IsCompl p q` if and only if $\lnot(p \leftrightarrow q)$ |

The last identity has a short proof. The propositions $p$ and $q$ are complements if $p \land q$ is false and $p \lor q$ is true. In classical logic this says that exactly one of $p$ and $q$ holds, and that is $\lnot(p \leftrightarrow q)$. The instances `Prop.instDistribLattice`, `Prop.instBoundedOrder` and `Prop.linearOrder` hold the structure. The linear order needs classical logic: for each $p$ and $q$, either $p \to q$ or $q \to p$, because either $q$ is true or $p \to q$ holds vacuously when $p$ is false.

The same module has the pointwise forms for functions into a family of orders: `Pi.disjoint_iff`, `Pi.codisjoint_iff` and `Pi.isCompl_iff` say that `Disjoint f g` holds if and only if `Disjoint (f i) (g i)` holds for each $i$. A set `Set α` is a predicate `α → Prop`, so these lemmas and the lattice of Prop give the lattice of sets.

#### Orders from the core library

The core library of Lean has its own order classes, for example a class that says a relation is a linear order. The module `Mathlib.Order.Std` builds the Mathlib classes from them. The factories are `Preorder.ofStd`, `PartialOrder.ofStd` and `LinearOrder.ofStd`. Each takes a structure of arguments, `Preorder.OfStdArgs`, `PartialOrder.OfStdArgs` or `LinearOrder.OfStdArgs`, whose fields are filled in automatically when the instances of the core library are present. So a declaration `instance : LinearOrder X := .ofStd X` gives a linear order on a type with a lawful comparison. The fields `LinearOrder.OfStdArgs.min`, `LinearOrder.OfStdArgs.max` and `LinearOrder.OfStdArgs.decidableLE` record the data that the Mathlib class needs and the core class does not hold.

#### Finitely supported functions

The module `Mathlib.Order.Preorder.Finsupp` orders `ι →₀ M`, the functions $\iota \to M$ with finite support, pointwise. The instances `Finsupp.preorder`, `Finsupp.partialorder`, `Finsupp.semilatticeSup`, `Finsupp.semilatticeInf` and `Finsupp.lattice` need only a zero and the matching structure on $M$. The definition unfolds by `Finsupp.le_def`: $f \le g$ if and only if $f(i) \le g(i)$ for each $i$. The strict order unfolds by `Finsupp.lt_def`: $f < g$ if and only if $f \le g$ and $f(i) < g(i)$ for some $i$. The lattice operations are pointwise, by `Finsupp.sup_apply` and `Finsupp.inf_apply`.

The coercion to functions is an order embedding, `Finsupp.orderEmbeddingToFun`, and for a finite index type it is an order isomorphism, `Finsupp.orderIsoFunOnFinite`. The lemmas `Finsupp.coe_le_coe`, `Finsupp.coe_lt_coe`, `Finsupp.coe_mono` and `Finsupp.coe_strictMono` express the same fact one property at a time. The supports satisfy $\operatorname{supp}(f \sqcup g) \cup \operatorname{supp}(f \sqcap g) = \operatorname{supp}(f) \cup \operatorname{supp}(g)$, by `Finsupp.support_sup_union_support_inf`. For the proof, take $i$ outside $\operatorname{supp}(f) \cup \operatorname{supp}(g)$. Then $f(i) = g(i) = 0$, so the supremum and the infimum vanish at $i$. Conversely, take $i$ with $f(i) \ne 0$. If both $(f \sqcup g)(i)$ and $(f \sqcap g)(i)$ are $0$, then $0 \le f(i) \le 0$, and antisymmetry gives $f(i) = 0$, a contradiction. The case $g(i) \ne 0$ is the same. The lemma `Finsupp.support_inf_union_support_sup` is the same identity with the two terms of the union in the other order.

#### Unordered pairs

An element of `Sym2 α` is an unordered pair $\{a, b\}$. In a semilattice, `Sym2.sup` and `Sym2.inf` take the supremum and the infimum of the two entries. They are well defined because $\sqcup$ and $\sqcap$ are commutative. The lemmas `Sym2.sup_mk` and `Sym2.inf_mk` compute them on a pair, and `Sym2.inf_le_sup` says that the infimum is below the supremum in a lattice.

In a linear order, an unordered pair is the same as an ordered pair $(a, b)$ with $a \le b$. The equivalence `Sym2.sortEquiv` sends $\{a, b\}$ to $(\min(a,b), \max(a,b))$, and `Sym2.sortEquiv_apply_coe` states this. The lemma `Sym2.inf_eq_inf_and_sup_eq_sup` says that two pairs with the same minimum and the same maximum are equal. For the proof, write $s = \{a, b\}$ with $a \le b$. Then $\min s = a$ and $\max s = b$, so $s = \{\min s, \max s\}$, and the same holds for $t$.

#### The order on a quotient

Let $\alpha$ have a relation $\le$ and let $\approx$ be an equivalence relation on $\alpha$. The module `Mathlib.Order.Quotient` puts a preorder on the quotient $\alpha/{\approx}$. The relation $[x] \le [y]$ is the transitive closure of the relation "$x \le y$ or $x \approx y$", as `Quotient.le_def` states. It is the quotient in the category of preorders. The quotient map is monotone, by `Quotient.mk_monotone`, and a monotone function $f$ that is constant on the classes gives a monotone function on the quotient, by `Quotient.lift_monotone`. For the proof of the second fact, a chain of steps $x = x_0, x_1, \ldots, x_n = y$, each step an inequality or an equivalence, gives $f(x_0) \le f(x_1) \le \cdots \le f(x_n)$: a step $x_k \le x_{k+1}$ gives an inequality because $f$ is monotone, and a step $x_k \approx x_{k+1}$ gives an equality.

The transitive closure is necessary in general. In a linear order with order-connected classes it is not. Assume that $\alpha$ is a linear order and that each class is `Set.OrdConnected`. Then the relation "$x \le y$ or $x \approx y$" is already transitive, and `Quotient.mk_le_mk` says $[x] \le [y] \leftrightarrow x \le y \lor x \approx y$. For the proof, take $x \approx y$ and $y \le z$, and assume $z < x$. Then $y \le z < x$, and $z$ lies between two elements of one class. The class is order-connected, so $z \approx x$, and so $x \approx z$. The other mixed case is the same. The instance `Quotient.instLinearOrder` then makes the quotient a linear order, and `Quotient.mk_lt_mk` says $[x] < [y] \leftrightarrow x < y \land \lnot(x \approx y)$. Such a quotient is sometimes called a condensation of $\alpha$.

#### Restriction to an initial interval

Let $\alpha$ be a preorder and let $\pi : \alpha \to \mathrm{Type}$ be a family of types. The module `Mathlib.Order.Restriction` restricts a function $x : \prod_i \pi(i)$ to the interval $\{j \mid j \le a\}$. The map `Preorder.restrictLe a` uses the set `Set.Iic a`, and `Preorder.frestrictLe a` uses the finite set `Finset.Iic a` when the order is `LocallyFiniteOrderBot`. The maps `Preorder.restrictLe₂` and `Preorder.frestrictLe₂` restrict further from $b$ to $a$ when $a \le b$. They form a projective system: `Preorder.restrictLe₂_comp_restrictLe` says that restriction to $b$ and then to $a$ is restriction to $a$, and `Preorder.restrictLe₂_comp_restrictLe₂` composes two steps. The proof is a computation with the evaluation lemma `Preorder.restrictLe_apply`: both sides send $x$ to $i \mapsto x(i)$. The lemma `Preorder.dependsOn_restrictLe` says that the restriction depends only on the coordinates in `Set.Iic a`, in the sense of `DependsOn`.

#### Common errors

1. The order on Prop is implication, not equality of truth values. The goal `p ≤ q` asks for a proof of `p → q`, and `le_Prop_eq` rewrites it.
2. The order on a quotient is a transitive closure. The simple form `Quotient.mk_le_mk` needs a linear order and order-connected classes. In other cases, use `Quotient.le_def`.
3. The order on `ι →₀ M` is the pointwise order, not a lexicographic order or the order of the sizes of the supports. For a lexicographic order, use the synonym `Lex` of the next sections.

### Exercises

1. (A) Prove that Prop with implication is a linear order, and state where the proof needs classical logic.
2. (A) Compute `Sym2.sortEquiv` on the pair $\{5, 2\}$ in $\mathbb{N}$ and check `Sym2.inf_le_sup` on it.
3. (A) For $f, g : \mathbb{N} \to_0 \mathbb{N}$ with $f = 2\,\delta_0 + \delta_3$ and $g = \delta_0 + 4\,\delta_1$, compute $f \sqcup g$, $f \sqcap g$ and their supports, and check `Finsupp.support_sup_union_support_inf`.
4. (B) On $\mathbb{N}$, let the classes of $\approx$ be $\{0, 2\}$ and the singletons $\{n\}$ for the other $n$. Show that $[1] \le [0]$ in the quotient preorder, although neither $1 \le 0$ nor $1 \approx 0$ holds.
5. (B) Let $\approx$ on $\mathbb{Q}$ be $x \approx y \leftrightarrow \lfloor x \rfloor = \lfloor y \rfloor$. Show that the classes are order-connected and that the quotient linear order is isomorphic to $\mathbb{Z}$.
6. (B) Prove that the quotient preorder has the universal property of `Quotient.lift_monotone`: a monotone map that is constant on the classes factors in a unique way through the quotient map.

### Reference

<?reference?>
