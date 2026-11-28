---
title: Archimedean modules and the Hahn embedding
kind: api
modules:
  - Mathlib.Algebra.Order.Module.Archimedean
  - Mathlib.Algebra.Order.Module.HahnEmbedding
explains:
  E2: [ArchimedeanClass.mk_smul, FiniteArchimedeanClass.ball, FiniteArchimedeanClass.closedBall, FiniteArchimedeanClass.submodule, HahnEmbedding.ArchimedeanStrata, HahnEmbedding.ArchimedeanStrata.archimedeanClassMk_of_mem_stratum, HahnEmbedding.Seed, HahnEmbedding.Partial, HahnEmbedding.Partial.exists_domain_eq_top, hahnEmbedding_isOrderedModule]
  E1: auto
families: []
requires: [V04, V05]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Archimedean modules and the Hahn embedding

### Overview

A linearly ordered group is Archimedean if no nonzero element is infinitely small compared to another. In general, the elements fall into Archimedean classes: two elements are in the same class if each is bounded by a multiple of the other. The Hahn embedding theorem states that each linearly ordered abelian group embeds into a group of Hahn series with real coefficients, indexed by the Archimedean classes, with the lexicographic order. This section covers the Archimedean classes of an ordered module, the submodules that they define, and the module form of the Hahn embedding theorem over an Archimedean division ring. The classic theorem for groups is the case $K = \mathbb{Q}$ and $R = \mathbb{R}$.

### The library around it

#### Archimedean classes

Let $M$ be a linearly ordered additive group. For $a \in M$, `ArchimedeanClass.mk a` is its Archimedean class. The order of the classes is reversed with respect to the size: `ArchimedeanClass.mk_le_mk` states that $\operatorname{mk}(a) \le \operatorname{mk}(b)$ if and only if $|b| \le n |a|$ for some $n \in \mathbb{N}$. A larger element thus has a smaller class, and $0$ has the class $\top$ (`ArchimedeanClass.mk_eq_top_iff`). The strict form `ArchimedeanClass.mk_lt_mk` says that $\operatorname{mk}(a) < \operatorname{mk}(b)$ if and only if $n |b| < |a|$ for each $n$, so $b$ is infinitely small compared to $a$. The type `FiniteArchimedeanClass M` is the set of classes other than $\top$, that is, the classes of the nonzero elements, with `FiniteArchimedeanClass.mk a h` for $a \ne 0$. The order isomorphism `FiniteArchimedeanClass.withTopOrderIso` adds $\top$ back.

These definitions are in the order library. The file `Mathlib.Algebra.Order.Module.Archimedean` adds the action of scalars.

**Theorem.** Let $K$ be an Archimedean linearly ordered division ring and $M$ an ordered $K$-module. For $k \ne 0$ in $K$ and $a \in M$, the classes of $k a$ and $a$ are equal.

*Proof.* Since $K$ is Archimedean, $|k| \le n$ for some $n \in \mathbb{N}$, so $|k a| = |k| \, |a| \le n |a|$. This gives $\operatorname{mk}(a) \le \operatorname{mk}(k a)$. The same argument with $k^{-1}$ gives $|a| = |k^{-1} (k a)| \le m |k a|$ for some $m$, so $\operatorname{mk}(k a) \le \operatorname{mk}(a)$. $\square$

This is `ArchimedeanClass.mk_smul`. The inequality `ArchimedeanClass.mk_le_mk_smul` holds for each $k$, including $k = 0$.

#### Balls of classes

For a class $c$, the ball `FiniteArchimedeanClass.ball K c` is the set of elements that are $0$ or have a class strictly above $c$, that is, the elements that are infinitely small compared to the elements of class $c$. The closed ball `FiniteArchimedeanClass.closedBall K c` also contains the elements of class $c$. The membership lemmas are `FiniteArchimedeanClass.mem_ball_iff` and `FiniteArchimedeanClass.mem_closedBall_iff`.

By the theorem above, both sets are closed under scalars, and they are closed under sums since the class of $a + b$ is at least the minimum of the two classes. So they are submodules. The order library has the same sets as subgroups, `ArchimedeanClass.ballAddSubgroup` and `ArchimedeanClass.closedBallAddSubgroup`, and `FiniteArchimedeanClass.toAddSubgroup_ball` connects the two forms. The ball is strictly smaller than the closed ball (`FiniteArchimedeanClass.ball_lt_closedBall`), and both maps are strictly antitone in $c$ (`FiniteArchimedeanClass.ball_strictAnti`). More generally, an upper set $U$ of classes gives the submodule `FiniteArchimedeanClass.submodule K U` of the elements whose class is in $U$ or is $\top$, and the map $U \mapsto$ submodule is strictly antitone (`FiniteArchimedeanClass.submodule_strictAnti`).

#### Strata and seeds

The quotient of the closed ball by the ball is the part of $M$ of class exactly $c$. The library uses a complement in place of the quotient. The structure `HahnEmbedding.ArchimedeanStrata K M` is a family of submodules $S_c$, one for each class $c$, with $B_c \cap S_c = 0$ and $B_c + S_c = \bar B_c$, where $B_c$ is the ball and $\bar B_c$ is the closed ball. These are the fields `HahnEmbedding.ArchimedeanStrata.disjoint_ball_stratum` and `HahnEmbedding.ArchimedeanStrata.ball_sup_stratum_eq`. Such a family exists, since the lattice of submodules is modular and so each submodule has a complement in each larger one (`IsModularLattice.exists_disjoint_and_sup_eq`).

**Theorem.** Each nonzero element of the stratum $S_c$ has the class $c$, and $S_c$ is Archimedean.

*Proof.* Let $a \in S_c$ with $a \ne 0$. Since $a \in \bar B_c$, the class of $a$ is at least $c$. If it were strictly above $c$, then $a \in B_c \cap S_c = 0$, which is false. So all nonzero elements of $S_c$ have the same class, and in particular each is bounded by a multiple of each other. This is the Archimedean property. $\square$

These are `HahnEmbedding.ArchimedeanStrata.archimedeanClassMk_of_mem_stratum` and the instance `HahnEmbedding.ArchimedeanStrata.archimedean_stratum`. Elements of distinct strata have distinct classes, so the strata are independent (`HahnEmbedding.ArchimedeanStrata.iSupIndep_stratum`). Their sum is `HahnEmbedding.ArchimedeanStrata.baseDomain`, and it is the internal direct sum of the strata. In general it is not all of $M$.

A seed, `HahnEmbedding.Seed K M R`, is a family of strata with a strictly monotone linear map $\varphi_c : S_c \to R$ for each $c$, where $R$ is an Archimedean ordered $K$-module. The seed gives the coefficients of the embedding.

#### The Hahn embedding

The target is the type `Lex R⟦FiniteArchimedeanClass M⟧` of Hahn series: functions from the classes to $R$ with a well-founded support, with the lexicographic order. A series is positive if its coefficient at the least index of its support is positive. The least index is `HahnSeries.orderTop`.

**Theorem.** Let $K$ be an Archimedean division ring, $M$ a linearly ordered $K$-module and $R$ an Archimedean $K$-module. If a seed exists, then there is a strictly monotone linear map $f : M \to R⟦\Gamma⟧$, where $\Gamma$ is the set of finite classes, such that the class of $a$ is the least index of the support of $f(a)$ for each $a$.

*Proof.* On the base domain, define $f$ on $S_c$ by $f(a) = \varphi_c(a) t^c$, a series with one term, and extend it to the direct sum. A sum of elements of distinct strata has the class of the term of least class, and its image has that term as its leading term, so $f$ is strictly monotone on the base domain. Next, consider the partial linear maps that extend this map, are strictly monotone, send each element to a series whose least index is its class, and have a range that is closed under the truncation of series. A chain of such maps has an upper bound on the union, so by Zorn's lemma there is a maximal one. If its domain is not $M$, take $x$ outside the domain. The truncation property gives a series $f(x)$ that is the limit of the approximations of $x$ from the domain, and the extension to the domain plus $K x$ is again such a map. This contradicts maximality, so the domain is $M$. $\square$

This is `hahnEmbedding_isOrderedModule`. The partial maps are the type `HahnEmbedding.Partial seed`, a subtype of partial linear maps with the predicate `HahnEmbedding.IsPartial`. The base map is `HahnEmbedding.Seed.baseEmbedding`, the extension step is `HahnEmbedding.Partial.extend` with `HahnEmbedding.Partial.lt_extend`, and the upper bound of a chain is `HahnEmbedding.Partial.sSup`. The maximal element is `HahnEmbedding.Partial.exists_isMax`, and `HahnEmbedding.Partial.exists_domain_eq_top` states that some partial map is defined on all of $M$.

For $K = \mathbb{Q}$ and $R = \mathbb{R}$ a seed always exists: each stratum is an Archimedean group, so it embeds into $\mathbb{R}$ by Hölder's theorem (`Archimedean.exists_orderAddMonoidHom_real_injective`). The ring theory library uses this for `hahnEmbedding_isOrderedModule_rat` and, after a passage to the divisible hull, for the classic theorem `hahnEmbedding_isOrderedAddMonoid` on each linearly ordered abelian group.

#### Common errors

1. Reading `ArchimedeanClass.mk a ≤ ArchimedeanClass.mk b` as "$a$ is smaller than $b$". The order is reversed: a smaller class means a larger element, and $0$ has the greatest class.
2. Expecting `hahnEmbedding_isOrderedModule` to need no hypothesis on the coefficients. It assumes an instance `Nonempty (HahnEmbedding.Seed K M R)`, which is automatic only for $K = \mathbb{Q}$ and $R = \mathbb{R}$.
3. Treating the strata as canonical. A choice of complements is data in `HahnEmbedding.ArchimedeanStrata`, and the embedding depends on it.

### Exercises

1. (A) Describe the Archimedean classes of $\mathbb{Z}^2$ with the lexicographic order.
2. (A) Show that $\mathbb{R}$ has exactly one finite Archimedean class, and that $\mathbb{R}$ is Archimedean.
3. (B) Show that the class of $a + b$ is at least the minimum of the classes of $a$ and $b$, with equality when the two classes are different.
4. (B) Find the balls and the closed balls of $\mathbb{R}^2$ with the lexicographic order, and give two different families of strata.
5. (B) Show that `ArchimedeanClass.mk_smul` fails over the non-Archimedean field $\mathbb{R}(x)$ with the order where $x$ is larger than each real number.
6. (C) Show that the Hahn embedding of an Archimedean group $M$ is an order embedding into $\mathbb{R}$.

### Reference

<?reference?>
