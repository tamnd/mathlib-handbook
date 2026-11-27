---
title: W types and univariate polynomial functors
kind: theory
modules:
  - Mathlib.Data.W.Basic
  - Mathlib.Data.W.Cardinal
  - Mathlib.Data.W.Constructions
  - Mathlib.Data.PFunctor.Univariate.Basic
  - Mathlib.Data.PFunctor.Univariate.M
  - Mathlib.Data.QPF.Univariate.Basic
explains:
  E3: [WType, WType.equivSigma, WType.elim, WType.elim_injective, WType.depth, WType.infinite_of_nonempty_of_isEmpty, WType.cardinalMk_eq_sum, WType.cardinalMk_le_of_le, WType.cardinalMk_le_max_aleph0_of_finite, WType.Natα, WType.equivNat, PFunctor, PFunctor.Obj, PFunctor.W, PFunctor.M, PFunctor.M.dest_corec, PFunctor.M.bisim, QPF, QPF.Wequiv, QPF.recF_eq_of_Wequiv, QPF.Fix, QPF.Fix.rec_eq, QPF.Cofix, QPF.Cofix.bisim]
  E2: [WType.mk, WType.toSigma, WType.ofSigma, WType.depth_pos, WType.depth_lt_depth_mk, WType.cardinalMk_eq_sum_lift, WType.Natβ, WType.ofNat, WType.toNat, WType.leftInverse_nat, WType.rightInverse_nat, WType.NatαEquivPUnitSumPUnit, WType.Listα, WType.Listβ, WType.ofList, WType.toList, WType.equivList, PFunctor.A, PFunctor.B, PFunctor.Obj.mk, PFunctor.map, PFunctor.W.head, PFunctor.W.children, PFunctor.W.dest, PFunctor.W.mk, PFunctor.W.dest_mk, PFunctor.W.mk_dest, PFunctor.comp, PFunctor.liftp_iff, PFunctor.supp_eq, PFunctor.Approx.CofixA, PFunctor.Approx.Agree, PFunctor.Approx.AllAgree, PFunctor.MIntl, PFunctor.M.corec, PFunctor.M.head, PFunctor.M.children, PFunctor.M.dest, PFunctor.M.mk, PFunctor.M.dest_mk, PFunctor.M.mk_dest, PFunctor.M.IsBisimulation, PFunctor.M.bisim', PFunctor.M.corec_unique, QPF.P, QPF.abs, QPF.repr, QPF.abs_repr, QPF.abs_map, QPF.lawfulFunctor, QPF.recF, QPF.Wrepr, QPF.Wsetoid, QPF.Fix.rec, QPF.Fix.mk, QPF.Fix.dest, QPF.Fix.ind_rec, QPF.Fix.rec_unique, QPF.Fix.mk_dest, QPF.Fix.dest_mk, QPF.Fix.ind, QPF.Mcongr, QPF.IsPrecongr, QPF.Cofix.corec, QPF.Cofix.dest, QPF.Cofix.dest_corec, QPF.Cofix.bisim', QPF.IsUniform, QPF.suppPreservation_iff_uniform, QPF.comp, QPF.quotientQPF]
  E1: auto
families: []
requires: [V01.C03, V24.C02, V31.C01, V33.C05, V33.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## W types and univariate polynomial functors

### Overview

The natural numbers, lists and binary trees are inductive types. Each element is a node with a label, and the label fixes how many children the node has. A W type collects all such trees for a given family of labels and arities. It is the general well-founded tree type of Martin-Löf type theory, and many inductive types are W types up to an equivalence.

A polynomial functor packs the same data, a type of shapes and a type of positions for each shape, as a functor: $X \mapsto \Sigma_a (B\,a \to X)$. Its initial algebra is the W type, and its final coalgebra is the type of possibly infinite trees, the M type. Streams and the sequences of Chapter 5 are M types up to equivalence.

Polynomial functors are closed under composition, but not under quotients. A multiset of children is a list of children up to permutation, and a list is polynomial while a multiset is not. A quotient of a polynomial functor (QPF) is a functor with an abstraction map from a polynomial functor onto it. Mathlib builds the initial algebra and the final coalgebra of each QPF as quotients of the W type and of the M type. Section 2 extends this to functors in several variables, which is the form that the datatype packages need.

### Definitions

**Definition (W type).** Let $\alpha$ be a type of labels and $\beta : \alpha \to \mathrm{Type}$ the arity of each label. The W type $W\beta$ is the inductive type with one constructor: for $a : \alpha$ and $f : \beta\,a \to W\beta$, the tree $\mathrm{mk}\ a\ f$ is in $W\beta$.

A label $a$ with empty $\beta\,a$ is a leaf, because $\mathrm{mk}\ a\ f$ needs no children. A label with $\beta\,a = \mathrm{Bool}$ has two children. Since the constructor is inductive, each tree is well-founded: each path from the root reaches a leaf after finitely many steps.

**Definition (Depth).** Suppose that each $\beta\,a$ is finite. The depth of a tree is $\mathrm{depth}(\mathrm{mk}\ a\ f) = 1 + \max_{i \in \beta a} \mathrm{depth}(f\,i)$, where the maximum over an empty type is $0$. So a leaf has depth $1$.

**Definition (Polynomial functor).** A polynomial functor $P$ is a pair of a type $A$ of shapes and a family $B : A \to \mathrm{Type}$ of positions. Its object map sends a type $X$ to $P\,X = \Sigma_{a : A} (B\,a \to X)$, and its map sends $g : X \to Y$ and $\langle a, f \rangle$ to $\langle a, g \circ f \rangle$. The W type of $P$ is $W B$, with $\mathrm{W.dest} : P.W \to P\,(P.W)$ and $\mathrm{W.mk} : P\,(P.W) \to P.W$.

**Definition (M type).** For a polynomial functor $P$, the approximations $\mathrm{CofixA}\ n$ are trees cut at depth $n$: $\mathrm{CofixA}\ 0$ has one element, and an element of $\mathrm{CofixA}(n + 1)$ is a shape $a$ with a map $B\,a \to \mathrm{CofixA}\ n$. The M type $P.M$ is the type of sequences $(x_n)$ with $x_n : \mathrm{CofixA}\ n$ such that each $x_n$ is the cut of $x_{n+1}$ at depth $n$.

The M type has a head, children, a destructor $\mathrm{M.dest} : P.M \to P\,(P.M)$ and a constructor $\mathrm{M.mk}$, and these are inverse to each other. For a coalgebra $g : \beta \to P\,\beta$, the map $\mathrm{M.corec}\ g : \beta \to P.M$ unfolds a seed into a tree.

**Definition (Quotient of a polynomial functor).** A functor $F$ is a QPF when there are a polynomial functor $P$ and maps $\mathrm{abs} : P\,X \to F\,X$ and $\mathrm{repr} : F\,X \to P\,X$ for each type $X$, such that $\mathrm{abs}(\mathrm{repr}\ x) = x$ and $\mathrm{abs}(P.\mathrm{map}\ g\ p) = g \mathbin{<\$>} \mathrm{abs}\ p$. So $\mathrm{abs}$ is a surjective natural transformation, and $\mathrm{repr}$ is a section that need not be natural.

**Definition (Equivalence of W trees).** For a QPF $F$ with polynomial functor $P$, the relation $\mathrm{Wequiv}$ on $P.W$ is the least equivalence relation with two closure properties. First, if $f\,i$ and $f'\,i$ are related for each $i$, then $\mathrm{mk}\ a\ f$ and $\mathrm{mk}\ a\ f'$ are related. Second, if $\mathrm{abs}\langle a, f \rangle = \mathrm{abs}\langle a', f' \rangle$, then $\mathrm{mk}\ a\ f$ and $\mathrm{mk}\ a'\ f'$ are related. The type $\mathrm{Fix}\ F$ is the quotient of $P.W$ by this relation.

**Definition (Cofix).** A relation $r$ on $P.M$ is a precongruence when $r\ x\ y$ implies that $\mathrm{abs}$ of the destructs of $x$ and $y$ agree after the quotient by $r$. Two M trees are congruent when some precongruence relates them. The type $\mathrm{Cofix}\ F$ is the quotient of $P.M$ by congruence.

### Theorems and proofs

**Proposition (Trees as pairs).** The maps $\mathrm{mk}\ a\ f \mapsto \langle a, f \rangle$ and $\langle a, f \rangle \mapsto \mathrm{mk}\ a\ f$ are inverse equivalences between $W\beta$ and $\Sigma_a (\beta\,a \to W\beta)$.

*Proof.* Both composites are the identity on constructors: a tree $\mathrm{mk}\ a\ f$ goes to $\langle a, f \rangle$ and back to $\mathrm{mk}\ a\ f$, and a pair $\langle a, f \rangle$ goes to $\mathrm{mk}\ a\ f$ and back to $\langle a, f \rangle$. Each tree is a constructor application, and each pair is a pair. $\square$

**Lemma (Injective folds).** Let $\gamma$ be a type and $h : \Sigma_a (\beta\,a \to \gamma) \to \gamma$ injective. The fold $\mathrm{elim}\ h : W\beta \to \gamma$, given by $\mathrm{elim}\ h\ (\mathrm{mk}\ a\ f) = h\langle a, \mathrm{elim}\ h \circ f \rangle$, is injective.

*Proof.* Induction on the first tree $\mathrm{mk}\ a_1\ f_1$. Take any second tree $\mathrm{mk}\ a_2\ f_2$ with the same image. Then $h\langle a_1, \mathrm{elim}\ h \circ f_1 \rangle = h\langle a_2, \mathrm{elim}\ h \circ f_2 \rangle$. Injectivity of $h$ gives $a_1 = a_2$ and $\mathrm{elim}\ h \circ f_1 = \mathrm{elim}\ h \circ f_2$. So $\mathrm{elim}\ h\ (f_1\,i) = \mathrm{elim}\ h\ (f_2\,i)$ for each $i$, and the induction hypothesis for the child $f_1\,i$ gives $f_1\,i = f_2\,i$. So $f_1 = f_2$ and the trees are equal. $\square$

**Theorem (Cardinality of a W type).** The cardinal $\kappa_W = \#(W\beta)$ satisfies $\kappa_W = \sum_a \kappa_W^{\#(\beta a)}$. It is the least cardinal $\kappa$ with $\sum_a \kappa^{\#(\beta a)} \leq \kappa$.

*Proof.* The equation follows from the equivalence of trees and pairs: the cardinal of a sigma type is the sum of the cardinals of the fibers, and the cardinal of $\beta\,a \to W\beta$ is $\kappa_W^{\#(\beta a)}$. For the minimality, let $\kappa = \#\gamma$ with $\sum_a \kappa^{\#(\beta a)} \leq \kappa$. The left side is the cardinal of $\Sigma_a (\beta\,a \to \gamma)$, so there is an injection $h$ from this type into $\gamma$. By the lemma, $\mathrm{elim}\ h : W\beta \to \gamma$ is injective, so $\kappa_W \leq \kappa$. $\square$

**Corollary (Finite arities).** If each $\beta\,a$ is finite, then $\#(W\beta) \leq \max(\#\alpha, \aleph_0)$.

*Proof.* If $\alpha$ is empty, there are no trees and the claim holds. Otherwise let $m = \max(\#\alpha, \aleph_0)$, an infinite cardinal. For each $a$, the exponent $\#(\beta\,a)$ is finite, so $m^{\#(\beta a)} \leq m$. Then $\sum_a m^{\#(\beta a)} \leq \#\alpha \cdot \sup_a m^{\#(\beta a)} \leq m \cdot m = m$. The theorem gives $\#(W\beta) \leq m$. $\square$

**Proposition (Infinite W types).** If there is a label $a$ with $\beta\,a$ nonempty and a label $b$ with $\beta\,b$ empty, then $W\beta$ is infinite.

*Proof.* The labels differ: $a \neq b$, because $\beta\,a$ is nonempty and $\beta\,b$ is empty. Define $t_0 = \mathrm{mk}\ b\ f_\emptyset$, where $f_\emptyset$ is the empty function, and $t_{n+1} = \mathrm{mk}\ a\ (\lambda\,i.\ t_n)$. Show $t_n \neq t_m$ for $n \neq m$ by induction on $n$. If one index is $0$ and the other is not, the root labels are $b$ and $a$, which differ. If $t_{n+1} = t_{m+1}$, the children agree; since $\beta\,a$ is nonempty, this gives $t_n = t_m$, so $n = m$ by the induction hypothesis. So $n \mapsto t_n$ is an injection from $\mathbb{N}$ into $W\beta$. $\square$

**Theorem (Bisimulation for M types).** Let $R$ be a relation on $P.M$ such that $R\ x\ y$ implies $\mathrm{M.dest}\ x = \langle a, f \rangle$ and $\mathrm{M.dest}\ y = \langle a, f' \rangle$ with the same shape $a$ and with $R\ (f\,i)\ (f'\,i)$ for each $i$. Then $R\ x\ y$ implies $x = y$.

*Proof.* An element of $P.M$ is its sequence of approximations, so it suffices to show that $x_n = y_n$ for each $n$ and each related pair. Induction on $n$ for all related pairs. For $n = 0$, $\mathrm{CofixA}\ 0$ has one element. For $n + 1$: by construction, the approximation of depth $n + 1$ of a tree with destruct $\langle a, f \rangle$ is the shape $a$ with the map $i \mapsto (f\,i)_n$. For a related pair, both trees have the shape $a$, and the induction hypothesis for the related pairs $(f\,i, f'\,i)$ gives $(f\,i)_n = (f'\,i)_n$ for each $i$. So $x_{n+1} = y_{n+1}$. $\square$

With this theorem, $\mathrm{M.dest}(\mathrm{M.corec}\ g\ x) = P.\mathrm{map}(\mathrm{M.corec}\ g)(g\ x)$ determines $\mathrm{M.corec}\ g$: any other $f$ with the same equation is related to it by $R\ u\ v :\iff \exists x,\ u = f\,x \wedge v = \mathrm{M.corec}\ g\ x$, and $R$ satisfies the hypothesis. So $P.M$ is a final coalgebra.

**Lemma (Recursion respects the equivalence).** Let $F$ be a QPF and $g : F\,X \to X$. Define $\mathrm{recF}\ g : P.W \to X$ by $\mathrm{recF}\ g\ (\mathrm{mk}\ a\ f) = g(\mathrm{abs}\langle a, \mathrm{recF}\ g \circ f \rangle)$. If $\mathrm{Wequiv}\ u\ v$, then $\mathrm{recF}\ g\ u = \mathrm{recF}\ g\ v$.

*Proof.* Induction on the derivation of $\mathrm{Wequiv}\ u\ v$. Case of children: $u = \mathrm{mk}\ a\ f$, $v = \mathrm{mk}\ a\ f'$, and the induction hypothesis gives $\mathrm{recF}\ g \circ f = \mathrm{recF}\ g \circ f'$; apply $g \circ \mathrm{abs}$. Case of abs: $\mathrm{abs}\langle a, f \rangle = \mathrm{abs}\langle a', f' \rangle$. Naturality of abs gives $\mathrm{abs}\langle a, \mathrm{recF}\ g \circ f \rangle = \mathrm{recF}\ g \mathbin{<\$>} \mathrm{abs}\langle a, f \rangle$, and the same for $a', f'$. The two right sides are equal, so the values of $\mathrm{recF}\ g$ agree. Case of transitivity: compose the two equations. $\square$

**Theorem (Fix is an initial algebra).** For a QPF $F$ on one universe, the map $\mathrm{Fix.mk} : F(\mathrm{Fix}\ F) \to \mathrm{Fix}\ F$ and the recursor $\mathrm{Fix.rec}\ g$ satisfy $\mathrm{Fix.rec}\ g\ (\mathrm{Fix.mk}\ x) = g(\mathrm{Fix.rec}\ g \mathbin{<\$>} x)$, and $\mathrm{Fix.rec}\ g$ is the unique map with this equation.

*Proof.* By the lemma, $\mathrm{recF}\ g$ descends to a map $\mathrm{Fix.rec}\ g$ on the quotient. To define $\mathrm{Fix.mk}$, pick a W tree for each class with $\mathrm{Wrepr}$, apply $\mathrm{repr}$ to $x$, and build the node. The equation follows from the definition of $\mathrm{recF}$, from $\mathrm{abs} \circ \mathrm{repr} = \mathrm{id}$, and from the naturality of abs, after checking that the chosen trees are equivalent to the given ones. For uniqueness, let $h$ satisfy the equation. Each class has a tree $\mathrm{mk}\ a\ f$, and the class of this tree is $\mathrm{Fix.mk}(\mathrm{abs}\langle a, \bar f \rangle)$, where $\bar f$ takes classes of children. Induction on the tree and the equation for $h$ and for $\mathrm{Fix.rec}\ g$ give $h = \mathrm{Fix.rec}\ g$ on this class. $\square$

Dually, $\mathrm{Cofix}\ F$ has $\mathrm{Cofix.dest}(\mathrm{Cofix.corec}\ g\ x) = \mathrm{Cofix.corec}\ g \mathbin{<\$>} g\ x$, and a relation $r$ with $r\ x\ y \Rightarrow \mathrm{Liftr}\ r\ (\mathrm{dest}\ x)\ (\mathrm{dest}\ y)$ implies equality. The proof reduces to the bisimulation for M types through the quotient.

### Examples

**Example (Natural numbers).** Take the labels $\{\mathrm{zero}, \mathrm{succ}\}$ with arities $\mathrm{Empty}$ and $\mathrm{Unit}$. The tree for $2$ is $\mathrm{mk}\ \mathrm{succ}(\lambda\_.\ \mathrm{mk}\ \mathrm{succ}(\lambda\_.\ \mathrm{mk}\ \mathrm{zero}\ f_\emptyset))$. The depth of the leaf is $0 + 1 = 1$, so the tree for $n$ has depth $n + 1$, and the tree for $2$ has depth $3$. The cardinal equation reads $\kappa = \kappa^0 + \kappa^1 = 1 + \kappa$, which $\aleph_0$ satisfies, and the corollary gives $\#W \leq \max(2, \aleph_0) = \aleph_0$.

**Example (Binary trees).** Take the labels $\{\mathrm{leaf}, \mathrm{node}\}$ with arities $\mathrm{Empty}$ and $\mathrm{Bool}$. The tree $\mathrm{node}(\mathrm{leaf}, \mathrm{node}(\mathrm{leaf}, \mathrm{leaf}))$ has depth $1 + \max(1, 1 + \max(1, 1)) = 3$. A tree of depth at most $n + 1$ is a leaf or a node with two trees of depth at most $n$. So the counts $c_n$ of trees of depth at most $n$ satisfy $c_1 = 1$ and $c_{n+1} = 1 + c_n^2$, which gives $c_2 = 2$ and $c_3 = 5$. The proposition on infinite W types and the corollary give $\#W = \aleph_0$.

**Example (Streams as an M type).** Take the polynomial functor with shapes $\alpha$ and one position for each shape. Then $P\,X = \alpha \times X$ up to equivalence, and an element of $P.M$ is a head with one child, for ever. The approximation of depth $3$ of the stream $0, 1, 2, \dots$ is the cut tree $0 \to 1 \to 2 \to \mathrm{continue}$. The coalgebra $g(n) = \langle n, \lambda\_.\ n + 1 \rangle$ gives this stream as $\mathrm{M.corec}\ g\ 0$.

**Example (Multisets as a QPF).** Take the polynomial functor of lists, with shapes $\mathbb{N}$ and positions $\mathrm{Fin}\ n$. Let $\mathrm{abs}\langle n, f \rangle$ be the multiset $\{f\,0, \dots, f(n-1)\}$. The pairs $\langle 2, [1, 2] \rangle$ and $\langle 2, [2, 1] \rangle$ have the same image. The type $\mathrm{Fix}$ of this QPF is the type of finitely branching trees whose children are unordered.

**Counterexample (Infinite arity without leaves).** Take one label with arity $\mathbb{N}$. There is no leaf, so the W type is empty: a tree would need an infinite descending path. The M type of the same polynomial functor has exactly one element, the infinite tree.

### The library around it

::: mathlib
`WType` · `Mathlib.Data.W.Basic`

`WType β` has the constructor `WType.mk`. `WType.toSigma`, `WType.ofSigma` and `WType.equivSigma` give the equivalence with pairs, and `WType.elim` with `WType.elim_injective` gives injective folds. `WType.depth`, `WType.depth_pos` and `WType.depth_lt_depth_mk` need finite arities. `WType.infinite_of_nonempty_of_isEmpty` is the proposition on infinite W types. The module also gives an `Encodable` instance when the labels form an encodable finite type and the arities are encodable finite types; its proof counts the trees of bounded depth.

<?decl WType.equivSigma?>
:::

::: mathlib
`WType.cardinalMk_le_of_le` · `Mathlib.Data.W.Cardinal`

`WType.cardinalMk_eq_sum` and `WType.cardinalMk_eq_sum_lift` give the cardinal equation. `WType.cardinalMk_le_of_le` is the minimality, and `WType.cardinalMk_le_max_aleph0_of_finite` is the corollary.

<?decl WType.cardinalMk_le_of_le?>
:::

::: mathlib
`WType.equivNat` · `Mathlib.Data.W.Constructions`

`WType.Natα` and `WType.Natβ` are the labels and arities of the natural numbers, with `WType.ofNat`, `WType.toNat`, `WType.leftInverse_nat`, `WType.rightInverse_nat`, `WType.equivNat` and `WType.NatαEquivPUnitSumPUnit`. `WType.Listα`, `WType.Listβ`, `WType.ofList`, `WType.toList` and `WType.equivList` do the same for lists.

<?decl WType.equivNat?>
:::

::: mathlib
`PFunctor` · `Mathlib.Data.PFunctor.Univariate.Basic`

`PFunctor` has the fields `PFunctor.A` and `PFunctor.B`, and `PFunctor.Obj` is the object map, with `PFunctor.Obj.mk` and `PFunctor.map`. `PFunctor.W` is the W type, with `PFunctor.W.head`, `PFunctor.W.children`, `PFunctor.W.dest`, `PFunctor.W.mk`, `PFunctor.W.dest_mk` and `PFunctor.W.mk_dest`. `PFunctor.comp` composes, and `PFunctor.liftp_iff` and `PFunctor.supp_eq` describe predicate lifting and support.

<?decl PFunctor.W?>
:::

::: mathlib
`PFunctor.M` · `Mathlib.Data.PFunctor.Univariate.M`

`PFunctor.Approx.CofixA`, `PFunctor.Approx.Agree` and `PFunctor.Approx.AllAgree` give the approximations, and `PFunctor.MIntl` is the structure behind `PFunctor.M`. The interface is `PFunctor.M.head`, `PFunctor.M.children`, `PFunctor.M.dest`, `PFunctor.M.mk`, `PFunctor.M.dest_mk`, `PFunctor.M.mk_dest`, `PFunctor.M.corec` and `PFunctor.M.dest_corec`. `PFunctor.M.bisim`, `PFunctor.M.bisim'`, `PFunctor.M.IsBisimulation` and `PFunctor.M.corec_unique` give finality.

<?decl PFunctor.M.bisim?>
:::

::: mathlib
`QPF.Fix.rec_eq` · `Mathlib.Data.QPF.Univariate.Basic`

The class `QPF` has the fields `QPF.P`, `QPF.abs`, `QPF.repr`, `QPF.abs_repr` and `QPF.abs_map`, and `QPF.lawfulFunctor` derives the functor laws. `QPF.recF`, `QPF.Wequiv`, `QPF.recF_eq_of_Wequiv`, `QPF.Wrepr` and `QPF.Wsetoid` build `QPF.Fix`, with `QPF.Fix.mk`, `QPF.Fix.dest`, `QPF.Fix.rec`, `QPF.Fix.rec_eq`, `QPF.Fix.rec_unique`, `QPF.Fix.ind_rec`, `QPF.Fix.ind`, `QPF.Fix.mk_dest` and `QPF.Fix.dest_mk`. `QPF.IsPrecongr` and `QPF.Mcongr` build `QPF.Cofix`, with `QPF.Cofix.corec`, `QPF.Cofix.dest`, `QPF.Cofix.dest_corec`, `QPF.Cofix.bisim` and `QPF.Cofix.bisim'`. `QPF.comp` and `QPF.quotientQPF` give closure under composition and quotients, and `QPF.IsUniform` with `QPF.suppPreservation_iff_uniform` treats the support.

<?decl QPF.Fix.rec_eq?>
:::

Common errors of a learner: The first error is to expect a leaf to have depth $0$; Mathlib adds one at each node, so a leaf has depth $1$. The second error is to apply `QPF.Fix` to a functor that changes the universe; it needs `F : Type u → Type u`. The third error is to assume that `QPF.repr` is natural; only `QPF.abs` is. The fourth error is to prove an equation in `PFunctor.M` by induction; M trees can be infinite, and `PFunctor.M.bisim` is the tool.

### Exercises

1. (A) Write the tree of $3$ in the W type of the natural numbers and compute its depth. Hint: each $\mathrm{succ}$ node adds one to the depth of its child.
2. (A) List the binary trees of depth at most $2$ and check the count $c_2 = 2$. Hint: a tree of depth $2$ is a node with two leaves.
3. (A) Show that the W type with one label of arity $\mathrm{Empty}$ has exactly one element. Hint: use the equivalence with pairs; a function from $\mathrm{Empty}$ is unique.
4. (B) Show from the cardinal equation that the W type of lists over a type $\gamma$ with $\#\gamma = \kappa \geq \aleph_0$ has cardinal $\kappa$. Hint: the labels are $\mathrm{nil}$ and $\mathrm{cons}\ x$ for $x : \gamma$, with arities $0$ and $1$.
5. (B) Prove $\mathrm{depth}(f\,i) < \mathrm{depth}(\mathrm{mk}\ a\ f)$ for each $i$. Hint: the depth of a child is at most the maximum, and the node adds one.
6. (B) For the polynomial functor of streams, show that two M trees with the same head at each position are equal. Hint: use the relation "the heads of all iterated children agree" in the bisimulation theorem.
7. (C) Show that the W type with labels $\mathbb{N}$, arity $\mathrm{Empty}$ at $0$ and arity $\mathbb{N}$ at each $n > 0$ has cardinal $2^{\aleph_0}$. Hint: use the cardinal equation for the lower bound and the minimality with $\kappa = 2^{\aleph_0}$ for the upper bound.

### Notes and history

W types come from the type theory of Martin-Löf, where they give well-founded trees for each signature. The view of inductive and coinductive types as initial algebras and final coalgebras of polynomial functors, under the name of containers, comes from Abbott, Altenkirch and Ghani in 2003 and 2005. Avigad, Carneiro and Hudon introduced quotients of polynomial functors in 2019 to give datatypes with quotient constructors, such as multisets of children, in Lean.

The Mathlib files are by these authors, read from their headers: `Mathlib.Data.W.Basic` by Jeremy Avigad, `Mathlib.Data.W.Cardinal` by Chris Hughes, `Mathlib.Data.W.Constructions` by Joseph Hua, `Mathlib.Data.PFunctor.Univariate.Basic` by Jeremy Avigad, `Mathlib.Data.PFunctor.Univariate.M` by Simon Hudon, and `Mathlib.Data.QPF.Univariate.Basic` by Jeremy Avigad.

### Reference

<?reference?>
