---
title: Direct limits of modules and rings
kind: api
modules:
  - Mathlib.Algebra.Colimit.DirectLimit
  - Mathlib.Algebra.Colimit.Module
  - Mathlib.Algebra.Colimit.Ring
  - Mathlib.Algebra.Colimit.Finiteness
  - Mathlib.Algebra.Colimit.TensorProduct
explains:
  E2: [Module.DirectLimit, Module.DirectLimit.exists_of, Module.DirectLimit.exists_eq_of_of_eq, Module.DirectLimit.linearEquiv, DirectLimit.exists_eq_zero, Ring.DirectLimit.of.zero_exact, Field.DirectLimit.field, Module.fgSystem.equiv, Submodule.FG.exists_rTensor_fg_inclusion_eq]
  E1: auto
families: []
requires: [V05, V06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Direct limits of modules and rings

### Overview

A direct limit glues a family of modules along maps between them. The index set $\iota$ is a preorder, there is a module $G_i$ for each $i$, and there is a linear map $f_{ij} : G_i \to G_j$ for each $i \le j$. When $\iota$ is directed and the maps are compatible, the direct limit is the union of the $G_i$ where an element of $G_i$ and its image in $G_j$ are the same point. The rational numbers are the direct limit of the groups $\frac{1}{n!}\mathbb{Z}$, and each module is the direct limit of its finitely generated submodules. Mathlib has two models. `Module.DirectLimit` and `Ring.DirectLimit` are quotients of a free object and work for each system. The generic type `DirectLimit` is a quotient of the disjoint union and works only for directed systems, but its equality is explicit. This section covers the two models, the criteria for equality, and the use of direct limits to reduce statements to finitely generated modules.

### The library around it

#### Directed systems

A family of maps `f i j h : G i → G j` is a directed system, `DirectedSystem G f`, when $f_{ii}$ is the identity and $f_{jk} \circ f_{ij} = f_{ik}$. The two laws are `DirectedSystem.map_self` and `DirectedSystem.map_map`. Most results also need the class `IsDirectedOrder ι`: each two indices have a common upper bound. Some need `Nonempty ι`, since the limit over the empty index set is $0$ and has no element $0$ that comes from a component.

#### The module model

The type `Module.DirectLimit G f` is the quotient of the direct sum $\bigoplus_i G_i$ by the congruence `Module.DirectLimit.moduleCon f`. This congruence is the smallest module congruence that identifies $x \in G_i$ with $f_{ij}(x) \in G_j$. The quotient uses the congruences of Chapter 1 and not a submodule, so the construction works over a semiring. The definition needs no order condition, and it is the colimit for each system.

The map from a component is `Module.DirectLimit.of R ι G f i`, and `Module.DirectLimit.of_f` says that $x$ and $f_{ij}(x)$ have the same image. The universal property is `Module.DirectLimit.lift`: a family of linear maps $g_i : G_i \to P$ with $g_j \circ f_{ij} = g_i$ gives a linear map from the limit, with `Module.DirectLimit.lift_of`. Two maps from the limit are equal if they agree on each component (`Module.DirectLimit.hom_ext`). A compatible family of maps between two systems gives `Module.DirectLimit.map`, and a family of equivalences gives `Module.DirectLimit.congr`. The same API exists for abelian groups, with `AddCommGroup.DirectLimit` and `AddCommGroup.DirectLimit.lift`.

For a directed index set, each element of the limit comes from a component.

**Theorem.** Let $\iota$ be directed and nonempty. Each $z$ in the direct limit is $\operatorname{of}_i(x)$ for some $i$ and some $x \in G_i$.

*Proof.* The set of $z$ that come from a component contains $0$, since $\iota$ is nonempty. It contains each $\operatorname{of}_i(x)$. Let $z = \operatorname{of}_i(x)$ and $z' = \operatorname{of}_j(y)$, and take $k$ with $i \le k$ and $j \le k$. Then $z + z' = \operatorname{of}_k(f_{ik}(x) + f_{jk}(y))$. So the set is closed under sums, and it is all of the limit, since the elements $\operatorname{of}_i(x)$ generate it. $\square$

This is `Module.DirectLimit.exists_of`. The induction principle `Module.DirectLimit.induction_on` uses it. The equality criterion is the second main fact.

**Theorem.** Let $\iota$ be directed and let $f$ be a directed system. If $x, y \in G_i$ have the same image in the direct limit, then $f_{ij}(x) = f_{ij}(y)$ for some $j \ge i$.

*Proof.* Let $\sim$ be the relation on the pairs $(i, x)$ with $(i, x) \sim (j, y)$ if $x$ and $y$ have the same image in some common upper stage. Since $\iota$ is directed and the maps are compatible, $\sim$ is an equivalence relation, and the quotient of the pairs by $\sim$ is a module. It satisfies the universal property, so it is equivalent to `Module.DirectLimit G f` by an equivalence that sends $\operatorname{of}_i(x)$ to the class of $(i, x)$. Thus the images of $x$ and $y$ are equal only if $(i, x) \sim (i, y)$. $\square$

This is `Module.DirectLimit.exists_eq_of_of_eq`. The case $y = 0$ is `Module.DirectLimit.of.zero_exact`. The explicit quotient in the proof is the generic `DirectLimit`, and the equivalence is `Module.DirectLimit.linearEquiv`. A consequence: if each $g_i$ is injective, then `Module.DirectLimit.lift` is injective (`Module.DirectLimit.lift_injective`).

#### The generic model

The generic `DirectLimit G f` is the quotient of the sigma type $\Sigma_i G_i$ by the relation of the proof above. It is defined in the order library for each directed system of functions. The file `Mathlib.Algebra.Colimit.DirectLimit` puts the algebraic structures on it, from a multiplication up to a field. Each operation is computed in a common stage: `DirectLimit.add_def` and `DirectLimit.mul_def` say that $[i, x] + [i, y] = [i, x + y]$ and $[i, x] [i, y] = [i, x y]$. The maps of the system can be of any type of morphism, for example linear maps or ring maps, with a class such as `LinearMapClass`. The equality criterion is direct: `DirectLimit.exists_eq_zero` states that $[i, x] = 0$ if and only if $f_{ij}(x) = 0$ for some $j \ge i$, and `DirectLimit.exists_eq_one` is the form for monoids.

The universal properties are in the namespaces of the structure: `DirectLimit.Module.of` and `DirectLimit.Module.lift` for modules, `DirectLimit.Ring.lift` for rings, and `DirectLimit.Algebra.lift` for algebras. The function `DirectLimit.lift` is the map for plain types, and the lemmas such as `DirectLimit.lift_add` and `DirectLimit.lift_mul` say that it keeps the operations.

#### Rings and fields

The type `Ring.DirectLimit G f` is the direct limit of a system of commutative rings. It is the quotient of the free commutative ring on $\Sigma_i G_i$ by the relations that make each component map a ring map and identify $x$ with $f_{ij}(x)$. The API is the same as for modules: `Ring.DirectLimit.of`, `Ring.DirectLimit.lift`, `Ring.DirectLimit.exists_of`, `Ring.DirectLimit.map` and `Ring.DirectLimit.congr`. For a directed system of ring maps, `Ring.DirectLimit.of.zero_exact` states that $\operatorname{of}_i(x) = 0$ implies $f_{ij}(x) = 0$ for some $j \ge i$, and `Ring.DirectLimit.ringEquiv` identifies the ring with the generic model. If each $f_{ij}$ is injective, each component map is injective (`Ring.DirectLimit.of_injective`).

**Theorem.** A direct limit of fields over a directed nonempty index set is a field.

*Proof.* The limit is not the zero ring, since $1 \ne 0$ in each $G_i$ and the equality criterion keeps it so. Let $p \ne 0$. Then $p = \operatorname{of}_i(x)$ for some $i$ and $x \in G_i$, and $x \ne 0$. Put $q = \operatorname{of}_i(x^{-1})$. Then $p q = \operatorname{of}_i(x x^{-1}) = 1$. $\square$

This is `Field.DirectLimit.field`, with the inverse `Field.DirectLimit.inv` and the law `Field.DirectLimit.mul_inv_cancel`. It is a definition and not an instance, so it must be installed as a local instance where it is needed. An algebraic closure is often built as such a limit of finite extensions.

#### Reduction to finitely generated modules

Let `Module.fgSystem R M` be the system of finitely generated submodules of $M$, ordered by inclusion, with the inclusions as maps. The index set is directed, since $N_1 + N_2$ is finitely generated.

**Theorem.** Each module $M$ is the direct limit of its finitely generated submodules.

*Proof.* The inclusions $N \to M$ are compatible, so they give a map from the limit to $M$. It is surjective, since each $m \in M$ is in the finitely generated submodule $Rm$. It is injective by `Module.DirectLimit.lift_injective`, since each inclusion is injective. $\square$

This is `Module.fgSystem.equiv`, and `Module.fgSystem.equiv_comp_of` says that it restricts to the inclusion on each $N$. The theorem lets a statement about all modules come from the finitely generated case, when the statement commutes with direct limits. The tensor product commutes with direct limits, by `TensorProduct.directLimitLeft`. From this, `Submodule.FG.exists_rTensor_fg_inclusion_eq` states: let $N \le P$ be finitely generated and let $x, y \in N \otimes M$ have the same image in $P \otimes M$; then they have the same image in $N' \otimes M$ for some finitely generated $N'$ with $N \le N'$. The proof writes $P$ as the limit of its finitely generated submodules that contain $N$ and applies the equality criterion to the limit $P \otimes M$. Results on flat modules use this to reduce to finitely generated submodules.

#### Common errors

1. Using `Module.DirectLimit.exists_of` or `Module.DirectLimit.of.zero_exact` without the order hypotheses. They need `IsDirectedOrder ι`, and the first also needs `Nonempty ι`. For a system that is not directed, the limit is still defined, but the equality criterion is false.
2. Expecting `Field.DirectLimit.field` to be found by instance search. It is a definition. Install it as a local instance before the field operations.
3. Proving the equality criterion by hand from the definition as a quotient of the direct sum. Move to the generic model with `Module.DirectLimit.linearEquiv`, where the relation is explicit.

### Exercises

1. (A) Show that the direct limit of the system $\mathbb{Z} \xrightarrow{2} \mathbb{Z} \xrightarrow{2} \mathbb{Z} \to \cdots$ is $\mathbb{Z}[1/2]$.
2. (A) Show that the direct limit of a system over $\iota$ with a greatest element $i_0$ is $G_{i_0}$.
3. (B) Let $\iota = \{a, b\}$ with no order relation between $a$ and $b$. Find the direct limit and show that the equality criterion does not apply.
4. (B) Show that the direct limit of the groups $\mathbb{Z}/p^n$ with the maps $x \mapsto p x$ is the Prüfer group $\mathbb{Z}[1/p] / \mathbb{Z}$.
5. (B) Show that a direct limit of torsion free modules over a domain, over a directed index set, is torsion free.
6. (C) Show that $M$ is flat if $N \otimes M \to P \otimes M$ is injective for each finitely generated submodule $N \le P$, with `Submodule.FG.exists_rTensor_fg_inclusion_eq`.

### Reference

<?reference?>
