---
title: Multivariate functors and datatypes
kind: theory
modules:
  - Mathlib.Data.TypeVec
  - Mathlib.Control.Functor.Multivariate
  - Mathlib.Data.PFunctor.Multivariate.Basic
  - Mathlib.Data.PFunctor.Multivariate.M
  - Mathlib.Data.PFunctor.Multivariate.W
  - Mathlib.Data.QPF.Multivariate.Basic
  - Mathlib.Data.QPF.Multivariate.Constructions.Cofix
  - Mathlib.Data.QPF.Multivariate.Constructions.Comp
  - Mathlib.Data.QPF.Multivariate.Constructions.Const
  - Mathlib.Data.QPF.Multivariate.Constructions.Fix
  - Mathlib.Data.QPF.Multivariate.Constructions.Prj
  - Mathlib.Data.QPF.Multivariate.Constructions.Quot
  - Mathlib.Data.QPF.Multivariate.Constructions.Sigma
explains:
  E3: [TypeVec, TypeVec.Arrow, TypeVec.append1, TypeVec.append1_drop_last, TypeVec.splitFun, MvFunctor, MvFunctor.LiftP, MvFunctor.supp, LawfulMvFunctor, MvPFunctor, MvPFunctor.Obj, MvPFunctor.liftP_iff, MvPFunctor.supp_eq, MvPFunctor.WPath, MvPFunctor.W, MvPFunctor.wRec_eq, MvPFunctor.M, MvPFunctor.M.dest_corec, MvQPF, MvQPF.comp_map, MvQPF.Fix, MvQPF.Fix.rec_eq, MvQPF.mvqpfFix, MvQPF.Cofix, MvQPF.Cofix.bisim, MvQPF.Prj.mvqpf, MvQPF.Comp]
  E2: [TypeVec.id, TypeVec.comp, TypeVec.drop, TypeVec.last, TypeVec.drop_append1, TypeVec.last_append1, TypeVec.appendFun, TypeVec.dropFun, TypeVec.lastFun, TypeVec.appendFun_comp, MvFunctor.map, MvFunctor.LiftR, MvFunctor.ofEquiv, MvPFunctor.map, MvPFunctor.const, MvPFunctor.comp, MvPFunctor.drop, MvPFunctor.last, MvPFunctor.wp, MvPFunctor.wMk, MvPFunctor.wRec, MvPFunctor.wMk', MvPFunctor.wDest', MvPFunctor.M.Path, MvPFunctor.mp, MvPFunctor.M.corec, MvPFunctor.M.dest, MvPFunctor.M.mk, MvPFunctor.M.bisim, MvQPF.P, MvQPF.abs, MvQPF.repr, MvQPF.abs_repr, MvQPF.abs_map, MvQPF.id_map, MvQPF.lawfulMvFunctor, MvQPF.liftR_iff, MvQPF.supp_eq, MvQPF.IsUniform, MvPFunctor.instMvQPFObj, MvQPF.recF, MvQPF.WEquiv, MvQPF.recF_eq_of_wEquiv, MvQPF.Fix.map, MvQPF.Fix.rec, MvQPF.Fix.mk, MvQPF.Fix.dest, MvQPF.Fix.rec_unique, MvQPF.Fix.ind, MvQPF.IsPrecongr, MvQPF.Mcongr, MvQPF.Cofix.corec, MvQPF.Cofix.dest, MvQPF.Cofix.mk, MvQPF.Cofix.dest_corec, MvQPF.Cofix.bisim', MvQPF.mvqpfCofix, MvQPF.Comp.inst, MvQPF.Const, MvQPF.Const.mvqpf, MvQPF.Prj, MvQPF.quotientQPF, MvQPF.Quot1, MvQPF.relQuot, MvQPF.Sigma, MvQPF.Pi, MvQPF.Sigma.inst, MvQPF.Pi.inst, MvQPF.liftP_iff]
  E1: auto
families: []
requires: [V01.C03, V24.C02, V33.C05, V33.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Multivariate functors and datatypes

### Overview

The type `List α` has a parameter `α`. As a fixed point it solves $X \cong 1 + \alpha \times X$, a functor in two variables: the parameter $\alpha$ and the recursive slot $X$. A rose tree, whose children form a list of trees, nests one fixed point inside another. So functors must take several type arguments, and a fixed point must again be a functor in the other arguments.

This section gives that theory. A type vector is a finite family of types indexed by `Fin2 n`, and a multivariate functor maps type vectors to types. Polynomial functors and their quotients carry over, with positions sorted by the argument they belong to. The W and M constructions become functors in the parameters. The fixed point of a QPF in $n + 1$ variables is a QPF in $n$ variables, so fixed points nest.

Projections, constants, compositions, sums, products, quotients and the two fixed points give QPF descriptions of datatypes. This is the method of Avigad, Carneiro and Hudon.

### Definitions

**Definition (Type vector).** A type vector of length $n$ is a function $\alpha : \mathrm{Fin2}\ n \to \mathrm{Type}$. An arrow $\alpha \Rightarrow \beta$ is a family of functions $f_i : \alpha_i \to \beta_i$, one for each index $i$. Arrows have an identity and a composition $g \circledcirc f$, given index by index.

**Definition (Append, drop and last).** For $\alpha$ of length $n$ and a type $\beta$, the vector $\alpha ::: \beta$ of length $n + 1$ has $\beta$ at the index $\mathrm{fz}$ and $\alpha_i$ at the index $\mathrm{fs}\ i$. For $\gamma$ of length $n + 1$, the vector $\mathrm{drop}\ \gamma$ is $i \mapsto \gamma_{\mathrm{fs}\,i}$ and the type $\mathrm{last}\ \gamma$ is $\gamma_{\mathrm{fz}}$. For arrows $f : \mathrm{drop}\ \gamma \Rightarrow \mathrm{drop}\ \gamma'$ and $g : \mathrm{last}\ \gamma \to \mathrm{last}\ \gamma'$, the arrow $\mathrm{splitFun}\ f\ g$ is $g$ at $\mathrm{fz}$ and $f_i$ at $\mathrm{fs}\ i$. On appended vectors, Mathlib calls it $\mathrm{appendFun}\ f\ g$.

So the new type sits at index $\mathrm{fz}$, although it is written last. The recursive slot of a datatype is this argument.

**Definition (Multivariate functor).** A multivariate functor of arity $n$ is a map $F$ from type vectors of length $n$ to types with a map $f \mathbin{<\$\$>} x : F\beta$ for each arrow $f : \alpha \Rightarrow \beta$ and $x : F\alpha$. It is lawful when the identity arrow acts as the identity and the map respects composition.

**Definition (Lifting and support).** For predicates $p_i$ on $\alpha_i$, $\mathrm{LiftP}\ p\ x$ holds when $x$ is the image under the inclusions of an element of $F$ applied to the subtypes $\{a : \alpha_i \mid p_i\,a\}$. The support of $x$ at index $i$ is the set of $a : \alpha_i$ such that $p_i\,a$ holds for each $p$ with $\mathrm{LiftP}\ p\ x$. $\mathrm{LiftR}$ uses subtypes of pairs.

**Definition (Multivariate polynomial functor).** A multivariate polynomial functor of arity $n$ is a type $A$ of shapes with a type vector $B\,a$ of positions for each shape. Its object map is $P\alpha = \Sigma_{a : A} (B\,a \Rightarrow \alpha)$, and the map is postcomposition with the arrow.

For $P$ of arity $n + 1$, the polynomial functor $\mathrm{drop}\ P$ keeps the positions of the first $n$ indices, and the univariate functor $\mathrm{last}\ P$ keeps the positions of the last index.

**Definition (W type of a polynomial functor).** Let $P$ have arity $n + 1$. The shapes of the W type are the trees of the univariate W type of $\mathrm{last}\ P$. For such a tree $t$ and an index $i$, a path $\mathrm{WPath}\ t\ i$ is either a position of index $i$ at the root, or a choice of child $j$ with a path in the child. The W type is the polynomial functor $\mathrm{wp}$ with these shapes and positions, and $P.W\,\alpha = \mathrm{wp}\,\alpha$.

So an element of $P.W\,\alpha$ is a well-founded tree shape and a value of $\alpha_i$ at each data position of index $i$ in the tree. The M type uses the M type of $\mathrm{last}\ P$ for the shapes in the same way.

**Definition (Multivariate QPF).** A multivariate functor $F$ is a QPF when it has a polynomial functor $P$ of the same arity, maps $\mathrm{abs} : P\alpha \to F\alpha$ and $\mathrm{repr} : F\alpha \to P\alpha$ with $\mathrm{abs}(\mathrm{repr}\ x) = x$, and $\mathrm{abs}(f \mathbin{<\$\$>} p) = f \mathbin{<\$\$>} \mathrm{abs}\ p$.

**Definition (Fixed points).** Let $F$ be a QPF of arity $n + 1$ with polynomial functor $P$. The type $\mathrm{Fix}\ F\ \alpha$ is the quotient of $P.W\,\alpha$ by the least equivalence relation that is closed under equal children and under equal $\mathrm{abs}$ images, as in Section 1. The type $\mathrm{Cofix}\ F\ \alpha$ is the quotient of $P.M\,\alpha$ by the largest precongruence. Both are functors of arity $n$ in $\alpha$.

**Definition (Basic QPFs).** The projection $\mathrm{Prj}\ i$ sends $\alpha$ to $\alpha_i$. The constant functor $\mathrm{Const}\ n\ A$ sends each $\alpha$ to $A$. The composition of $F$ of arity $n$ with $G_1, \dots, G_n$ of arity $m$ sends $\alpha$ to $F(i \mapsto G_i\,\alpha)$. The sigma and pi of a family $F_a$ send $\alpha$ to $\Sigma_a F_a\,\alpha$ and to $\Pi_a F_a\,\alpha$. The quotient of $F$ by a family of relations $R_\alpha$ that is compatible with the map sends $\alpha$ to $F\alpha / R_\alpha$.

### Theorems and proofs

**Lemma (Vectors split).** For each $\gamma$ of length $n + 1$, $\mathrm{drop}\ \gamma ::: \mathrm{last}\ \gamma = \gamma$. For each $\alpha$ and $\beta$, $\mathrm{drop}(\alpha ::: \beta) = \alpha$ and $\mathrm{last}(\alpha ::: \beta) = \beta$.

*Proof.* Two type vectors are equal when they agree at each index. At $\mathrm{fz}$, the left side of the first equation is $\mathrm{last}\ \gamma = \gamma_{\mathrm{fz}}$. At $\mathrm{fs}\ i$, it is $(\mathrm{drop}\ \gamma)_i = \gamma_{\mathrm{fs}\,i}$. Each element of $\mathrm{Fin2}(n + 1)$ is $\mathrm{fz}$ or $\mathrm{fs}\ i$, so the vectors agree. The other two equations hold by the definition of append, at each index. $\square$

**Proposition (Lifting in a polynomial functor).** For $P$ polynomial and $x = \langle a, f \rangle : P\alpha$, $\mathrm{LiftP}\ p\ x$ holds if and only if $p_i(f_i\,j)$ for each index $i$ and position $j$. The support of $x$ at $i$ is the image of $f_i$.

*Proof.* Suppose $\mathrm{LiftP}\ p\ x$, with $u = \langle a', h \rangle : P(\text{subtypes})$ that maps to $x$. The map keeps the shape, so $a' = a$ and $f_i\,j$ is the underlying value of $h_i\,j$, which satisfies $p_i$. Conversely, if each $f_i\,j$ satisfies $p_i$, the element $\langle a, j \mapsto \langle f_i\,j, \cdot \rangle \rangle$ maps to $x$. For the support: by the first part, the predicate "$b$ is in the image of $f_i$" lifts, so the support lies in the image. Each value $f_i\,j$ satisfies each lifted predicate by the first part, so the image lies in the support. $\square$

**Proposition (Functor laws of a QPF).** Each multivariate QPF is a lawful functor.

*Proof.* Let $x : F\alpha$ and write $x = \mathrm{abs}(\mathrm{repr}\ x)$. For the identity, $\mathrm{id} \mathbin{<\$\$>} x = \mathrm{id} \mathbin{<\$\$>} \mathrm{abs}(\mathrm{repr}\ x) = \mathrm{abs}(\mathrm{id} \mathbin{<\$\$>} \mathrm{repr}\ x) = \mathrm{abs}(\mathrm{repr}\ x) = x$, by naturality of abs and the identity law of the polynomial functor. For the composition, $(g \circledcirc f) \mathbin{<\$\$>} x = \mathrm{abs}((g \circledcirc f) \mathbin{<\$\$>} \mathrm{repr}\ x) = \mathrm{abs}(g \mathbin{<\$\$>} f \mathbin{<\$\$>} \mathrm{repr}\ x)$, by the composition law of the polynomial functor, and naturality of abs, applied twice, turns this into $g \mathbin{<\$\$>} f \mathbin{<\$\$>} \mathrm{abs}(\mathrm{repr}\ x) = g \mathbin{<\$\$>} f \mathbin{<\$\$>} x$. $\square$

**Proposition (Projections are QPFs).** The projection $\mathrm{Prj}\ i$ is a QPF with the polynomial functor that has one shape and, at index $j$, one position if $j = i$ and none otherwise.

*Proof.* An element of $P\alpha$ is a family of maps from these positions, which is a single value $v : \alpha_i$. Let $\mathrm{abs}$ read this value and let $\mathrm{repr}\ v$ be the family that returns $v$ at the unique position. Then $\mathrm{abs}(\mathrm{repr}\ v) = v$. For an arrow $f$, $\mathrm{abs}(f \mathbin{<\$\$>} p)$ is $f_i$ applied to the value at the position of $p$, which is $f_i(\mathrm{abs}\ p) = f \mathbin{<\$\$>} \mathrm{abs}\ p$. $\square$

**Theorem (Recursion on Fix).** Let $F$ be a QPF of arity $n + 1$ and $g : F(\alpha ::: \beta) \to \beta$. The recursor $\mathrm{Fix.rec}\ g : \mathrm{Fix}\ F\ \alpha \to \beta$ satisfies $\mathrm{Fix.rec}\ g\ (\mathrm{Fix.mk}\ x) = g(\mathrm{appendFun}\ \mathrm{id}\ (\mathrm{Fix.rec}\ g) \mathbin{<\$\$>} x)$.

*Proof.* On W trees, define $\mathrm{recF}\ g$ by recursion: a tree with shape $a$, data $f'$ and children $f$ goes to $g(\mathrm{abs}\langle a, \mathrm{splitFun}\ f'\ (\mathrm{recF}\ g \circ f) \rangle)$. It is the same on equivalent trees, by induction on the derivation as in Section 1: the case of equal children uses the induction hypothesis, the case of equal abs images uses naturality of abs for the arrow $\mathrm{appendFun}\ \mathrm{id}\ (\mathrm{recF}\ g)$, and transitivity composes. So $\mathrm{recF}\ g$ descends to $\mathrm{Fix.rec}\ g$. The constructor $\mathrm{Fix.mk}\ x$ applies $\mathrm{repr}$ to $x$ and picks a W tree for each child. Unfolding $\mathrm{recF}$ once at this node, the chosen trees are representatives of their classes, and naturality of abs with $\mathrm{abs} \circ \mathrm{repr} = \mathrm{id}$ gives the right side. $\square$

**Theorem (Fixed points are QPFs).** For a QPF $F$ of arity $n + 1$ with polynomial functor $P$, the functor $\alpha \mapsto \mathrm{Fix}\ F\ \alpha$ is a QPF of arity $n$ with the polynomial functor $\mathrm{wp}$ of $P$.

*Proof.* By definition, $P.W\,\alpha = \mathrm{wp}\,\alpha$. Let $\mathrm{abs}$ be the quotient map $P.W\,\alpha \to \mathrm{Fix}\ F\ \alpha$, and let $\mathrm{repr}$ pick the canonical representative that the construction of $\mathrm{Fix.mk}$ uses. The representative of a class lies in the class, so $\mathrm{abs} \circ \mathrm{repr} = \mathrm{id}$. The map of $\mathrm{Fix}\ F$ is defined by the map of W trees on representatives, which is well defined because the map of W trees sends equivalent trees to equivalent trees. So the quotient map commutes with the maps, which is naturality of abs. $\square$

So Fix can be applied again to the result. This is how a rose tree, which contains a list of rose trees, gets a QPF description.

**Theorem (Bisimulation for Cofix).** Let $r$ be a relation on $\mathrm{Cofix}\ F\ \alpha$ such that $r\ x\ y$ implies $\mathrm{LiftR}(\mathrm{Eq} \oplus r)(\mathrm{dest}\ x)(\mathrm{dest}\ y)$, where the relation is equality at the first $n$ indices and $r$ at the last index. Then $r\ x\ y$ implies $x = y$.

*Proof.* The lifting in a QPF gives, for related $x, y$, one shape $a$ and data $f_0, f_1$ with $\mathrm{dest}\ x = \mathrm{abs}\langle a, f_0 \rangle$ and $\mathrm{dest}\ y = \mathrm{abs}\langle a, f_1 \rangle$, equal at the first $n$ indices and related by $r$ at the last. Pull $r$ back to a relation on M trees through the quotient, and close it under the congruence. The resulting relation is a precongruence: the abs images of the destructs agree after the quotient by it, because the last components are related and the others are equal. Two trees related by a precongruence are congruent, so they have the same class, and $x = y$. $\square$

### Examples

**Example (A type vector).** Let $\alpha = (\varnothing ::: \mathbb{N}) ::: \mathrm{Bool}$, where $\varnothing$ is the vector of length $0$. Then $\alpha_{\mathrm{fz}} = \mathrm{Bool}$ and $\alpha_{\mathrm{fs}\,\mathrm{fz}} = \mathbb{N}$. So $\mathrm{last}\ \alpha = \mathrm{Bool}$ and $\mathrm{drop}\ \alpha = \varnothing ::: \mathbb{N}$. The arrow $\mathrm{appendFun}(\mathrm{appendFun}\ !\ (\lambda n.\ n + 1))(\lambda b.\ \neg b)$, with $!$ the empty arrow, sends $(3, \mathrm{true})$ in the two slots to $(4, \mathrm{false})$.

**Example (Lists as a fixed point).** Take the polynomial functor of arity $2$ with shapes $\{\mathrm{nil}, \mathrm{cons}\}$. The shape $\mathrm{nil}$ has no positions. The shape $\mathrm{cons}$ has one position of the parameter index $\mathrm{fs}\ \mathrm{fz}$ and one position of the recursive index $\mathrm{fz}$. Then $P(\alpha ::: X) \cong 1 + \alpha \times X$. The univariate functor $\mathrm{last}\ P$ is the functor of natural numbers from Section 1, so a shape of $P.W$ is a length. A tree of length $2$ has two data paths: the root position, and the path through the child to its root position. For the list $[5, 7]$, the first path holds $5$ and the second holds $7$. No two W trees are identified here, because abs is the identity, so $\mathrm{Fix}$ of this QPF is the type of lists.

**Example (A quotient).** By the theorem on fixed points, the list functor $\alpha \mapsto \mathrm{List}\ \alpha$ is a QPF of arity $1$. Its quotient by permutation, with $[5, 7]$ and $[7, 5]$ in one class, is the multiset functor, and it is a QPF by the closure under quotients. Then the Fix of the functor $\alpha ::: X \mapsto \alpha \times \mathrm{Multiset}\ X$ is the type of finitely branching trees with labels in $\alpha$ and unordered children.

**Counterexample (A functor that is not a QPF).** The functor $F\,X = (X \to \mathrm{Prop}) \to \mathrm{Prop}$ of arity $1$ is not a QPF. Suppose that $P$ and a surjection $\mathrm{abs} : P\,X \to F\,X$ exist for each $X$. Let $\kappa$ be an infinite cardinal with $\#(B\,a) \leq \kappa$ for each shape $a$ and $\#A \leq \kappa$. Take $X$ with $\#X = \lambda = 2^\kappa$, so that $\lambda^\kappa = \lambda$. Then $\#(P\,X) \leq \kappa \cdot \lambda^\kappa = \lambda$, but $\#(F\,X) = 2^{2^\lambda} > \lambda$, so abs is not surjective. Mathlib does not state this negative result.

### The library around it

::: mathlib
`TypeVec.append1` · `Mathlib.Data.TypeVec`

`TypeVec n` is `Fin2 n → Type*`, and `TypeVec.Arrow` is written `⟹` in the scope `MvFunctor`, with `TypeVec.id` and `TypeVec.comp`. `TypeVec.append1` is written `:::`, with `TypeVec.drop`, `TypeVec.last`, `TypeVec.drop_append1`, `TypeVec.last_append1` and `TypeVec.append1_drop_last`. For arrows, `TypeVec.splitFun`, `TypeVec.appendFun`, `TypeVec.dropFun` and `TypeVec.lastFun` come with `TypeVec.appendFun_comp`.

<?decl TypeVec.append1?>
:::

::: mathlib
`MvFunctor` · `Mathlib.Control.Functor.Multivariate`

`MvFunctor.map` is written `<$$>`, and `LawfulMvFunctor` states the laws. `MvFunctor.LiftP`, `MvFunctor.LiftR` and `MvFunctor.supp` are the liftings and the support of the text, and `MvFunctor.ofEquiv` moves a functor along equivalences.

<?decl MvFunctor?>
:::

::: mathlib
`MvPFunctor.liftP_iff` · `Mathlib.Data.PFunctor.Multivariate.Basic`

`MvPFunctor n` has the fields `A` and `B`, with `MvPFunctor.Obj` and `MvPFunctor.map`. `MvPFunctor.const` and `MvPFunctor.comp` give constants and composition. `MvPFunctor.liftP_iff` and `MvPFunctor.supp_eq` are the proposition on lifting, and `MvPFunctor.drop` and `MvPFunctor.last` split a functor of arity `n + 1`.

<?decl MvPFunctor.liftP_iff?>
:::

::: mathlib
`MvPFunctor.wRec_eq` · `Mathlib.Data.PFunctor.Multivariate.W`

`MvPFunctor.WPath` gives the data paths, `MvPFunctor.wp` is the polynomial functor of W trees, and `MvPFunctor.W` is its object map. `MvPFunctor.wMk`, `MvPFunctor.wRec` and `MvPFunctor.wRec_eq` give the inductive interface, and `MvPFunctor.wMk'` and `MvPFunctor.wDest'` state it with appended vectors.

<?decl MvPFunctor.wRec_eq?>
:::

::: mathlib
`MvPFunctor.M.dest_corec` · `Mathlib.Data.PFunctor.Multivariate.M`

`MvPFunctor.M.Path` and `MvPFunctor.mp` build `MvPFunctor.M` from the univariate M type of `last`. `MvPFunctor.M.corec` takes `g : β → P (α ::: β)`, with `MvPFunctor.M.dest`, `MvPFunctor.M.mk`, `MvPFunctor.M.dest_corec` and the bisimulation `MvPFunctor.M.bisim`.

<?decl MvPFunctor.M.dest_corec?>
:::

::: mathlib
`MvQPF` · `Mathlib.Data.QPF.Multivariate.Basic`

`MvQPF` has the fields `MvQPF.P`, `MvQPF.abs`, `MvQPF.repr`, `MvQPF.abs_repr` and `MvQPF.abs_map`. `MvQPF.id_map`, `MvQPF.comp_map` and `MvQPF.lawfulMvFunctor` give the laws, `MvQPF.liftP_iff`, `MvQPF.liftR_iff` and `MvQPF.supp_eq` describe lifting and support, and `MvQPF.IsUniform` names the uniform case. `MvPFunctor.instMvQPFObj` makes each polynomial functor a QPF.

<?decl MvQPF?>
:::

::: mathlib
`MvQPF.Fix.rec_eq` · `Mathlib.Data.QPF.Multivariate.Constructions.Fix`

`MvQPF.recF`, `MvQPF.WEquiv` and `MvQPF.recF_eq_of_wEquiv` build `MvQPF.Fix`, with `MvQPF.Fix.map`, `MvQPF.Fix.mk`, `MvQPF.Fix.dest`, `MvQPF.Fix.rec`, `MvQPF.Fix.rec_eq`, `MvQPF.Fix.rec_unique` and `MvQPF.Fix.ind`. The instance `MvQPF.mvqpfFix` is the theorem that fixed points are QPFs.

<?decl MvQPF.Fix.rec_eq?>
:::

::: mathlib
`MvQPF.Cofix.bisim` · `Mathlib.Data.QPF.Multivariate.Constructions.Cofix`

`MvQPF.IsPrecongr` and `MvQPF.Mcongr` build `MvQPF.Cofix`, with `MvQPF.Cofix.corec`, `MvQPF.Cofix.dest`, `MvQPF.Cofix.mk` and `MvQPF.Cofix.dest_corec`. `MvQPF.Cofix.bisim` and `MvQPF.Cofix.bisim'` are the bisimulation principles, and `MvQPF.mvqpfCofix` makes `Cofix F` a QPF. The module also defines a tactic `mv_bisim`.

<?decl MvQPF.Cofix.bisim?>
:::

::: mathlib
`MvQPF.Prj.mvqpf` · `Mathlib.Data.QPF.Multivariate.Constructions.Prj`

`MvQPF.Prj` is the projection, and `MvQPF.Prj.mvqpf` is the proposition of the text. The sibling modules give `MvQPF.Const` with `MvQPF.Const.mvqpf`, `MvQPF.Comp` with `MvQPF.Comp.inst`, `MvQPF.Sigma` and `MvQPF.Pi` with `MvQPF.Sigma.inst` and `MvQPF.Pi.inst`, and quotients with `MvQPF.quotientQPF`, `MvQPF.Quot1` and the noncomputable `MvQPF.relQuot`.

<?decl MvQPF.Prj.mvqpf?>
:::

The index of this edition has no declaration for a datatype command that builds these QPFs from a declaration; in Mathlib, the constructions are used by hand.

Common errors of a learner: The first error is to look for the recursive slot at the highest index; `TypeVec.append1` puts the new type at `Fin2.fz`. The second error is to expect `MvQPF.repr` to be natural; only `MvQPF.abs` is. The third error is to apply `MvQPF.Fix` to a functor of arity `n`; it needs arity `n + 1` and returns a functor of arity `n`.

### Exercises

1. (A) For $\alpha = ((\varnothing ::: \mathbb{N}) ::: \mathrm{Bool}) ::: \mathrm{Unit}$, give $\alpha_{\mathrm{fz}}$, $\alpha_{\mathrm{fs}\,\mathrm{fz}}$ and $\alpha_{\mathrm{fs}(\mathrm{fs}\,\mathrm{fz})}$. Hint: each append pushes the older types one step up.
2. (A) Prove $\mathrm{splitFun}(\mathrm{dropFun}\ f)(\mathrm{lastFun}\ f) = f$ for each arrow $f$ between vectors of length $n + 1$. Hint: compare at $\mathrm{fz}$ and at $\mathrm{fs}\ i$.
3. (A) Show that the constant functor $\mathrm{Const}\ n\ A$ is a QPF with shapes $A$ and no positions. Hint: $\mathrm{abs}\langle a, \cdot \rangle = a$, and the map does not change the shape.
4. (B) For the list functor of the examples, count the data paths of a W tree of length $k$, and give the equivalence of $P.W\,\alpha$ with $\Sigma_k (\mathrm{Fin}\ k \to \alpha_{\mathrm{fz}})$ for the vector of length $1$. Hint: one path ends at each $\mathrm{cons}$ node.
5. (B) Prove that the support of a value in the projection $\mathrm{Prj}\ i$ at index $i$ is the singleton of the value, and empty at each $j \neq i$. Hint: use the proposition on lifting in a polynomial functor.
6. (B) Show that the composition of QPFs is a QPF. Hint: compose the polynomial functors, and let $\mathrm{abs}$ apply the inner abs maps under the outer one.
7. (C) Describe a QPF of arity $2$ whose Fix in the last index is the type of rose trees with labels in the parameter, and check that it uses Fix twice. Hint: the children of a node form a list, and the list is itself a Fix.

### Notes and history

The containers of Abbott, Altenkirch and Ghani, from 2003 and 2005, treat polynomial functors in several variables and their fixed points. Avigad, Carneiro and Hudon introduced quotients of polynomial functors in 2019, with type vectors, the W and M constructions in several variables, and the closure of QPFs under fixed points.

The Mathlib files are by these authors, read from their headers: `Mathlib.Data.TypeVec`, `Mathlib.Control.Functor.Multivariate` and `Mathlib.Data.PFunctor.Multivariate.M` by Jeremy Avigad, Mario Carneiro and Simon Hudon; `Mathlib.Data.PFunctor.Multivariate.Basic`, `Mathlib.Data.PFunctor.Multivariate.W`, `Mathlib.Data.QPF.Multivariate.Basic` and the constructions `Cofix`, `Comp`, `Fix` and `Quot` by Jeremy Avigad and Simon Hudon; and the constructions `Const`, `Prj` and `Sigma` by Simon Hudon.

### Reference

<?reference?>
