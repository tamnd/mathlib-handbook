---
title: Nerves and quasicategories
kind: theory
modules:
  - Mathlib.AlgebraicTopology.Quasicategory.Basic
  - Mathlib.AlgebraicTopology.Quasicategory.CompStruct
  - Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
  - Mathlib.AlgebraicTopology.Quasicategory.Nerve
  - Mathlib.AlgebraicTopology.Quasicategory.StrictBicategory
  - Mathlib.AlgebraicTopology.Quasicategory.StrictSegal
  - Mathlib.AlgebraicTopology.Quasicategory.TwoTruncated
  - Mathlib.AlgebraicTopology.Quasicategory.TwoTruncatedQuasicategory
  - Mathlib.AlgebraicTopology.SimplicialNerve
  - Mathlib.AlgebraicTopology.SimplicialSet.CoherentIso
  - Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
  - Mathlib.AlgebraicTopology.SimplicialSet.CompStructTruncated
  - Mathlib.AlgebraicTopology.SimplicialSet.HoFunctorMonoidal
  - Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
  - Mathlib.AlgebraicTopology.SimplicialSet.Nerve
  - Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
  - Mathlib.AlgebraicTopology.SimplicialSet.NerveCodiscrete
  - Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate
  - Mathlib.AlgebraicTopology.SimplicialSet.Path
  - Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal
explains:
  E3: [CategoryTheory.nerve, SSet.StrictSegal, CategoryTheory.Nerve.strictSegal, SSet.Quasicategory, CategoryTheory.Nerve.quasicategory, SSet.StrictSegal.quasicategory, SSet.HomotopyCategory, SSet.hoFunctor, CategoryTheory.nerveAdjunction, CategoryTheory.nerveFunctor.fullyfaithful]
  E2: [CategoryTheory.nerveMap, CategoryTheory.nerveFunctor, CategoryTheory.nerveEquiv, CategoryTheory.nerve.δ₀_mk₂_eq, CategoryTheory.nerve.homEquiv, CategoryTheory.nerve.edgeMk, SSet.StrictSegal.spineToSimplex, SSet.StrictSegal.spineEquiv, SSet.IsStrictSegal, SSet.Path, SSet.spine, SSet.Quasicategory.hornFilling, SSet.quasicategory_of_filler, SSet.quasicategory_iff_hasLiftingProperty, SSet.instQuasicategoryOfKanComplex, SSet.innerHornInclusions, SSet.innerFibrations, SSet.InnerFibration, SSet.quasicategory_iff_innerFibration, SSet.Edge, SSet.Edge.CompStruct, SSet.Edge.id, SSet.Edge.InvStruct, SSet.Edge.comp, SSet.Edge.compStruct, SSet.Edge.assoc, SSet.Edge.HomotopyL, SSet.Edge.CompStruct.unique, SSet.Truncated.Edge, SSet.Truncated.Edge.CompStruct, SSet.Truncated.Quasicategory₂, SSet.Truncated.HomotopicL, SSet.Truncated.HomotopicR, SSet.Truncated.HomotopyCategory₂, SSet.instQuasicategory₂ObjTruncatedOfNatNatTruncationOfQuasicategory, SSet.OneTruncation₂, SSet.Truncated.HomotopyCategory, SSet.Truncated.hoFunctor₂, SSet.HomotopyCategory.homMk, CategoryTheory.nerveFunctor.full, CategoryTheory.nerveFunctor.faithful, CategoryTheory.nerveFunctorCompHoFunctorIso, SSet.Truncated.nerve₂Adj, SSet.Truncated.liftOfStrictSegal, SSet.Truncated.hoFunctor.monoidal, SSet.Truncated.HomotopyCategory.BinaryProduct.iso, SSet.QCat, SSet.QCat.strictBicategory, CategoryTheory.SimplicialThickening, CategoryTheory.SimplicialNerve, SSet.coherentIso, CategoryTheory.WalkingIso, SSet.coherentIso.hom, SSet.coherentIso.invStructOfEqMapHom, CategoryTheory.Codiscrete.equivFun, PartialOrder.mem_nerve_nonDegenerate_iff_strictMono]
  E1: auto
families: []
requires: [V24.C01, V24.C02, V24.C04, V24.C05, V27.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Nerves and quasicategories

### Overview

The nerve turns a category into a simplicial set. Its $n$-simplices are the strings of $n$ composable arrows, its faces compose or drop arrows, and its degeneracies insert identities. A nerve has a special property: each inner horn has exactly one filler. Quasicategories keep the existence of inner horn fillers and drop the uniqueness. They are the model of $\infty$-categories of Joyal and Lurie.

This section defines the nerve and the strict Segal condition and proves that nerves are strict Segal and that they have unique inner horn fillers. It proves that the nerve functor is fully faithful and that it has a left adjoint, the homotopy category. It then defines quasicategories and inner fibrations, and reads the composition of edges up to homotopy, the coherent isomorphism and the simplicial nerve of a simplicial category.

### Definitions

For $0 \leq j \leq k \leq n$, write $j \to k$ for the unique arrow of the poset $[n]$, seen as a category.

**Definition (Nerve).** The *nerve* $N(C)$ of a category $C$ is the simplicial set with $N(C)_n$ the set of functors $[n] \to C$, and with $\theta^* F = F \circ \theta$ for $\theta : [m] \to [n]$. An $n$-simplex is a string $c_0 \xrightarrow{f_1} c_1 \to \cdots \xrightarrow{f_n} c_n$. The face $d_0$ drops $f_1$, the face $d_n$ drops $f_n$, the face $d_i$ for $0 < i < n$ replaces $f_i, f_{i+1}$ by $f_{i+1} f_i$, and $s_j$ inserts $\mathrm{id}_{c_j}$. A functor $G$ gives $N(G)$ by composition.

**Definition (Spine and strict Segal condition).** A *path* of length $n$ in a simplicial set $X$ is a sequence of vertices $x_0, \dots, x_n \in X_0$ and edges $e_1, \dots, e_n \in X_1$ with $d_1 e_j = x_{j-1}$ and $d_0 e_j = x_j$. The *spine* of $\sigma \in X_n$ is the path of its vertices and its edges from $j - 1$ to $j$. The simplicial set $X$ is *strict Segal* if the spine map $X_n \to \mathrm{Path}_n(X)$ is a bijection for every $n$.

**Definition (Homotopy category).** The *homotopy category* $hX$ of a simplicial set $X$ has the objects $X_0$. Its morphisms are generated by the edges $e : d_1 e \to d_0 e$ of $X$, with the relations $s_0 x = \mathrm{id}_x$ for $x \in X_0$ and $d_1 \tau = d_0 \tau \circ d_2 \tau$ for each $\tau \in X_2$.

**Definition (Quasicategory).** A simplicial set $X$ is a *quasicategory* if each map $\Lambda[n, i] \to X$ with $0 < i < n$ extends to $\Delta[n]$. A map $p : X \to Y$ is an *inner fibration* if it has the right lifting property against each inner horn inclusion $\Lambda[n, i] \to \Delta[n]$.

So $X$ is a quasicategory if and only if $X \to \Delta[0]$ is an inner fibration. A map $\Lambda[2,1] \to X$ is a pair of composable edges by Section 3 of Chapter 3, so the case $n = 2$ asks for a $2$-simplex that witnesses a composite.

**Definition (Homotopy of edges).** In a quasicategory, two edges $e, e' : x \to y$ are *left homotopic* if there is $\tau \in X_2$ with $d_2 \tau = e$, $d_0 \tau = s_0 y$ and $d_1 \tau = e'$. A $2$-simplex $\tau$ with $d_2 \tau = f$, $d_0 \tau = g$ and $d_1 \tau = h$ *witnesses* $h$ as a composite of $f$ and $g$.

### Theorems and proofs

**Lemma (Functors out of [n]).** A functor $F : [n] \to C$ is determined by the arrows $F(j - 1 \to j)$, $1 \leq j \leq n$, and each string of $n$ composable arrows arises from a functor.

*Proof.* Each arrow $j \to k$ of $[n]$ is the composite of the arrows $l - 1 \to l$ for $j < l \leq k$, and $F(j \to j)$ is an identity. So $F$ is fixed by the given arrows. Conversely, given $c_0 \xrightarrow{f_1} \cdots \xrightarrow{f_n} c_n$, put $F(j \to k) = f_k \cdots f_{j+1}$, with the empty composite the identity. Then $F(k \to l) F(j \to k) = F(j \to l)$, so $F$ is a functor. $\square$

**Theorem (Nerves are strict Segal).** For each category $C$, $N(C)$ is strict Segal.

*Proof.* A path of length $n$ in $N(C)$ is a sequence of objects and arrows $f_j : c_{j-1} \to c_j$, since a $1$-simplex of $N(C)$ is an arrow and its faces are its source and target. The spine of $F \in N(C)_n$ is the sequence $F(j-1 \to j)$. By the lemma the spine map is a bijection. $\square$

**Theorem (Unique inner horn fillers in a nerve).** Let $0 < i < n$. Each map $\Lambda[n, i] \to N(C)$ has exactly one extension to $\Delta[n]$. In particular $N(C)$ is a quasicategory.

*Proof.* By Section 3 of Chapter 3, $\Lambda[n, i]$ is the union of the faces $\partial_k \Delta[n]$ for $k \neq i$, and a map $u : \Lambda[n, i] \to N(C)$ is a family of compatible functors on these faces. An edge $(j, l)$ of $\Delta[n]$ lies in the horn if some $k \notin \{i, j, l\}$ exists. Write $u(j, l)$ for its image.

Case $n = 2$, $i = 1$. The horn holds the edges $(0,1)$ and $(1,2)$, with images $f$ and $g$. An extension is a functor $[2] \to C$ with these two arrows; by the lemma it exists and is unique, with third edge $g f$.

Case $n \geq 3$. Every edge $(j, l)$ lies in the horn, since $\{i, j, l\}$ has at most $3 < n + 1$ elements. Put $F(j \to l) = u(j, l)$ and $F(j \to j) = \mathrm{id}$. For $j < k < l$ the relation $F(j \to l) = F(k \to l) F(j \to k)$ holds when the triangle $(j, k, l)$ lies in the horn, because $u$ is a functor on a face that contains it. The triangle is outside the horn only when $\{i, j, k, l\} = [n]$, so $n = 3$ and $(j, k, l)$ is the face opposite $i$. If $i = 1$, then the triangles $(0,1,2)$, $(0,1,3)$ and $(1,2,3)$ lie in the horn, and $$F(0 \to 3) = F(1 \to 3) F(0 \to 1) = F(2 \to 3) F(1 \to 2) F(0 \to 1) = F(2 \to 3) F(0 \to 2).$$ The case $i = 2$ is symmetric, with the triangles $(0,1,2)$, $(0,2,3)$ and $(1,2,3)$. So $F$ is a functor $[n] \to C$. Its restriction to each face $\partial_k \Delta[n]$, $k \neq i$, has the same arrows as $u$, so it agrees with $u$ by the lemma. Any extension has the arrows $u(j, l)$, so it is $F$. $\square$

**Theorem (The nerve is fully faithful).** The functor $N : \mathbf{Cat} \to \mathbf{sSet}$ is fully faithful.

*Proof.* Faithful: $N(G)$ on $0$-simplices and $1$-simplices is $G$ on objects and arrows. Full: let $\varphi : N(C) \to N(D)$. Define $G$ on objects by $\varphi_0$ and on arrows by $\varphi_1$; $G$ preserves sources and targets since $\varphi$ commutes with $d_0$ and $d_1$, and identities since it commutes with $s_0$. For composable $f, g$, let $\tau \in N(C)_2$ be the string $(f, g)$. Then $\varphi_2(\tau)$ has faces $G f$, $G g$ and $G(g f)$, and a $2$-simplex of $N(D)$ is a commuting triangle, so $G(g f) = G g \circ G f$. Then $N(G)$ and $\varphi$ agree on $0$- and $1$-simplices. A map into a strict Segal simplicial set is fixed by its values on these, because the spine of $\varphi_n(\sigma)$ is the image of the spine of $\sigma$. So $\varphi = N(G)$. $\square$

**Theorem (Homotopy category and nerve).** For each simplicial set $X$ and category $C$, there is a bijection $\mathrm{Hom}_{\mathbf{Cat}}(hX, C) \cong \mathrm{Hom}_{\mathbf{sSet}}(X, N(C))$, natural in both variables. So $h$ is left adjoint to $N$, and $h N(C) \cong C$.

*Proof.* A functor $G : hX \to C$ is a map $x \mapsto G x$ on $X_0$ and $e \mapsto G e$ on $X_1$ with $G(s_0 x) = \mathrm{id}$ and $G(d_1 \tau) = G(d_0 \tau) G(d_2 \tau)$, by the presentation of $hX$. Given $G$, send $\sigma \in X_n$ to the functor $[n] \to C$ with $j \to k$ sent to $G$ of the edge $(j, k)$ of $\sigma$. It is a functor: the edge $(j, j)$ is degenerate, so it goes to an identity, and for $j < k < l$ the triangle $(j, k, l)$ of $\sigma$ gives $G(j \to l) = G(k \to l) G(j \to k)$. These maps commute with all $\theta^*$, since the edges of $\theta^* \sigma$ are edges of $\sigma$. Conversely, a map $\varphi : X \to N(C)$ gives $G$ on $X_0$ and $X_1$, and the relations hold because $\varphi$ sends a $2$-simplex to a commuting triangle and $s_0 x$ to an identity. The two constructions are inverse: by strict Segal, a map into $N(C)$ is fixed by its values on vertices and edges. Naturality is clear. For $h N(C) \cong C$: in $h N(C)$ the generators are the arrows of $C$ and the relations are the commuting triangles, which is a presentation of $C$. $\square$

### Examples

**Example (The nerve of the arrow category).** Let $[1]$ be the category with two objects $0, 1$ and one arrow $0 \to 1$ besides the identities. An $n$-simplex of $N([1])$ is a functor $[n] \to [1]$, that is a monotone map. So $N([1]) = \Delta[1]$, and this holds for each $[m]$: $N([m]) = \Delta[m]$. There are $n + 2$ monotone maps $[n] \to [1]$, namely $(0, \dots, 0, 1, \dots, 1)$ with $k$ zeros for $0 \leq k \leq n + 1$. A simplex is nondegenerate exactly when it is strictly monotone, so the nondegenerate simplices are $(0)$, $(1)$ and $(0,1)$, in dimensions $0$ and $1$ only. The $2$-simplices are $(0,0,0)$, $(0,0,1)$, $(0,1,1)$ and $(1,1,1)$, all degenerate: for instance $(0,0,1) = s_0 (0,1)$.

**Example (Filling Λ[2,1] in a nerve).** A map $\Lambda[2,1] \to N(C)$ is a pair $c_0 \xrightarrow{f} c_1 \xrightarrow{g} c_2$. Its unique filler is the string $(f, g)$, a $2$-simplex with $d_2 = f$, $d_0 = g$ and $d_1 = g f$. In $\Delta[1] = N([1])$, the horn with $f = (0,1)$ and $g = (1,1)$ has the filler $(0,1,1)$, whose third face is $(0,1)$.

**Counterexample (An outer horn in Δ[1]).** The outer horn $\Lambda[2,0]$ holds the edges $(0,1)$ and $(0,2)$. Send $(0,1)$ to the edge $(0,1)$ of $\Delta[1]$ and $(0,2)$ to the degenerate edge $(0,0)$. A filler would be a monotone map $a : [2] \to [1]$ with $a(0) = 0$, $a(1) = 1$ and $a(2) = 0$, which does not exist. So $\Delta[1]$ is a quasicategory without fillers for outer horns, and it is not a Kan complex.

**Example (The coherent isomorphism).** Let $\mathbb{I}$ be the category with two objects $0, 1$ and exactly one arrow between any two objects, so $0 \to 1$ is an isomorphism. Its nerve $J = N(\mathbb{I})$ has as $n$-simplices all sequences in $\{0, 1\}^{n+1}$, since a functor $[n] \to \mathbb{I}$ is fixed by its values on objects. A map $J \to X$ is an edge of $X$ with a full system of higher witnesses that it is invertible.

### The library around it

::: mathlib
`CategoryTheory.nerve` · `Mathlib.AlgebraicTopology.SimplicialSet.Nerve`

`nerve C` has `nerve C _⦋n⦌ = ComposableArrows C n`, and `nerveFunctor : Cat ⥤ SSet` sends a functor to `nerveMap`. `nerveEquiv` identifies the $0$-simplices with the objects, `nerve.homEquiv` identifies edges between two vertices with arrows, and `nerve.edgeMk` makes an edge from an arrow. The lemmas `nerve.δ₀_mk₂_eq`, `δ₁_mk₂_eq` and `δ₂_mk₂_eq` compute the faces of the $2$-simplex `ComposableArrows.mk₂ f g`, the last of them giving `f ≫ g` in the middle. `PartialOrder.mem_nerve_nonDegenerate_iff_strictMono` is the criterion of the first example for a poset, and `Codiscrete.equivFun` is the description of the nerve of a codiscrete category used in the last example.

<?decl CategoryTheory.nerve?>
:::

::: mathlib
`SSet.StrictSegal` · `Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal`

`SSet.Path X n` is the type of paths of length `n` and `SSet.spine X n : X _⦋n⦌ → Path X n` the spine map. `StrictSegal X` is data: an inverse `spineToSimplex` with the two inverse laws, and `spineEquiv` packs it as an equivalence; `IsStrictSegal X` is the mere existence. `Nerve.strictSegal C` is the first theorem. In the module `Quasicategory.StrictSegal`, `StrictSegal.quasicategory` says that each strict Segal simplicial set is a quasicategory: the filler is `spineToSimplex` of the spine of the horn. `Nerve.quasicategory` is the resulting instance for nerves, and `Nerve.cosk₂Iso` in `SimplicialSet.Coskeletal` says that a nerve is $2$-coskeletal.

<?decl SSet.StrictSegal?>
:::

::: mathlib
`CategoryTheory.nerveAdjunction` · `Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction`

`SSet.HomotopyCategory X` is a quotient of the free category on the reflexive quiver `OneTruncation₂` of the $2$-truncation, with `HomotopyCategory.homMk` for the morphism of an edge. `SSet.hoFunctor` is `truncation 2 ⋙ Truncated.hoFunctor₂`. `nerveAdjunction : hoFunctor ⊣ nerveFunctor` is the adjunction, built from `coskAdj 2` and the $2$-truncated adjunction `Truncated.nerve₂Adj`, whose proof uses `Truncated.liftOfStrictSegal`. `nerveFunctor.full`, `nerveFunctor.faithful` and `nerveFunctor.fullyfaithful` give the theorem on full faithfulness, and `nerveFunctorCompHoFunctorIso` is $h N \cong \mathrm{id}$. `Truncated.hoFunctor.monoidal` and `HomotopyCategory.BinaryProduct.iso` show that the homotopy category of a product of $2$-truncated simplicial sets is the product.

<?decl CategoryTheory.nerveAdjunction?>
:::

::: mathlib
`SSet.Quasicategory` · `Mathlib.AlgebraicTopology.Quasicategory.Basic`

`Quasicategory S` is a class with the field `hornFilling'` for `Λ[n + 2, i]` with `0 < i < Fin.last (n + 2)`; `Quasicategory.hornFilling` restates it with `n`, and `quasicategory_of_filler` lets one check fillers on faces. `quasicategory_iff_hasLiftingProperty` is the lifting form. The instance `instQuasicategoryOfKanComplex` says that a Kan complex is a quasicategory. In `InnerFibration`, `innerHornInclusions` is the class of inner horn inclusions, `innerFibrations` its right lifting class, `InnerFibration` the class of a map and `quasicategory_iff_innerFibration` the remark after the definition.

<?decl SSet.Quasicategory?>
:::

`SSet.Edge x₀ x₁` is an edge with prescribed vertices, `Edge.id` is `σ 0 x`, and `Edge.CompStruct e₀₁ e₁₂ e₀₂` is a $2$-simplex with faces `d₂ = e₀₁`, `d₀ = e₁₂` and `d₁ = e₀₂`; `SSet.Truncated.Edge` and `Truncated.Edge.CompStruct` are the $2$-truncated versions. `Edge.InvStruct` records an inverse. In a quasicategory, `Edge.comp` chooses a composite with the witness `Edge.compStruct`, `Edge.assoc` is associativity in the form of the inner $3$-horn, `Edge.HomotopyL e e'` is a `CompStruct e (id _) e'`, and `CompStruct.unique` says that two composites are homotopic. `Truncated.Quasicategory₂` asks for the fillers of the inner $2$- and $3$-horns in a $2$-truncated simplicial set, `HomotopicL` and `HomotopicR` are the homotopy relations, and `HomotopyCategory₂` has homotopy classes of edges as morphisms. The instance `instQuasicategory₂ObjTruncatedOfNatNatTruncationOfQuasicategory` says that the truncation of a quasicategory is one. The module header lists the comparison of `HomotopyCategory₂` with `HomotopyCategory` as work to do; the index of this edition has no declaration for it.

`SSet.QCat` is the category of quasicategories and `QCat.strictBicategory` the strict bicategory whose hom-categories are the homotopy categories of the internal homs. `WalkingIso` is the category $\mathbb{I}$, `SSet.coherentIso` its nerve $J$ and `coherentIso.hom` the forward edge; `coherentIso.invStructOfEqMapHom` says that an edge in the image of a map from $J$ has an inverse. `SimplicialThickening J` is the simplicial category of a linear order whose hom from $i$ to $j$ is the nerve of the poset of subsets of $[i, j]$ that contain both ends, and `SimplicialNerve C` has as $n$-simplices the simplicial functors from `SimplicialThickening (Fin (n + 1))` to `C`. The module header lists the identification of its low simplices and the theorem that it is a quasicategory when the hom objects are Kan complexes as projects; the index of this edition has no declaration for them.

Common errors of a learner:

- In `ComposableArrows`, the arrows are composed with `≫`, so the middle face of `mk₂ f g` is `f ≫ g`, that is $g f$.
- `StrictSegal X` is a structure with data, not a proposition. Use `IsStrictSegal X` for the property.
- `Quasicategory` asks only for inner horns. The fillers are not unique, so `Edge.comp` is a choice, and only its homotopy class is canonical.
- The homotopy category of a general simplicial set is built from paths of edges. The description by homotopy classes of single edges holds only for quasicategories.

### Exercises

1. (A) Describe $N(C)$ for a monoid $M$ seen as a one-object category, and give $d_0$, $d_1$, $d_2$ on $N(M)_2 = M^2$. *Hint:* $d_1(a, b)$ is the product of $a$ and $b$ in the order fixed by the convention of composition.
2. (A) Show that $N(C^{\mathrm{op}})$ is the simplicial set obtained from $N(C)$ by reversing each $[n]$. *Hint:* reverse the string of arrows.
3. (A) Compute the homotopy category of $\Lambda[2,1]$ and of $\partial\Delta[2]$. *Hint:* $\partial\Delta[2]$ has no $2$-simplex, so its homotopy category is free on three arrows.
4. (B) Show that $\Lambda[2,1]$ is not a quasicategory, and that $\partial\Delta[2]$ is not one. *Hint:* fill the identity of the horn.
5. (B) Prove that $N(C) \times N(D) \cong N(C \times D)$. *Hint:* a functor into a product is a pair of functors.
6. (B) Show that in $N(C)$ two edges $f, f' : x \to y$ are left homotopic if and only if $f = f'$. *Hint:* a $2$-simplex is a commuting triangle.
7. (C) Show that a simplicial set $X$ is isomorphic to the nerve of a category if and only if it is strict Segal. *Hint:* for the converse, build a category with objects $X_0$ and arrows $X_1$, with the composite of $f$ and $g$ the face $d_1$ of the $2$-simplex with spine $(f, g)$, and check associativity with $3$-simplices.

### Notes and history

Boardman and Vogt introduced the weak Kan condition, now the definition of a quasicategory, in 1973. Joyal developed the theory of quasicategories, and Lurie, *Higher Topos Theory* (2009), made them the standard model of $\infty$-categories; Mathlib cites it for the simplicial nerve. Mathlib cites Riehl and Verity for the strict bicategory of quasicategories.

The Mathlib Authors of `Quasicategory.Basic` are Johan Commelin, and of `Quasicategory.Nerve` and `Quasicategory.StrictSegal` Johan Commelin, Emily Riehl and Nick Ward. `InnerFibration` is by Jack McKoen. `Quasicategory.CompStruct`, `TwoTruncatedQuasicategory`, `SimplicialSet.Nerve`, `CompStructTruncated`, `HoFunctorMonoidal` and `NerveNondegenerate` are by Joël Riou, and `SimplicialSet.CompStruct` by Joël Riou and Arnoud van der Leer. `TwoTruncated` is by Julian Komaromy and Joël Riou, and `StrictBicategory` by Emily Riehl. `StrictSegal` is by Mario Carneiro, Emily Riehl, Joël Riou, Johan Commelin and Nick Ward. `Path`, `HomotopyCat` and `NerveAdjunction` are by Mario Carneiro, Emily Riehl and Joël Riou. `SimplicialNerve` is by Dagur Asgeirsson, `CoherentIso` by the Johns Hopkins Category Theory Seminar and Arnoud van der Leer, and `NerveCodiscrete` by Arnoud van der Leer.

### Reference

<?reference?>
