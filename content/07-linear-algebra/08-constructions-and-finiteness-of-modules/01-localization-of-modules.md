---
title: Localization of modules
kind: api
modules:
  - Mathlib.Algebra.Module.LocalizedModule.Basic
  - Mathlib.Algebra.Module.LocalizedModule.AtPrime
  - Mathlib.Algebra.Module.LocalizedModule.Away
  - Mathlib.Algebra.Module.LocalizedModule.Exact
  - Mathlib.Algebra.Module.LocalizedModule.Int
  - Mathlib.Algebra.Module.LocalizedModule.IsLocalization
  - Mathlib.Algebra.Module.LocalizedModule.Submodule
explains:
  E2: [LocalizedModule, IsLocalizedModule, LocalizedModule.mk_eq, LocalizedModule.mem_ker_mkLinearMap_iff, IsLocalizedModule.iso, IsLocalizedModule.map_exact, isLocalizedModule_iff_isLocalization', Submodule.localized'_eq_span, localizedQuotientEquiv]
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

## Localization of modules

### Overview

Let $R$ be a commutative ring and $S \subseteq R$ a multiplicative set. The localization $S^{-1}R$ is the ring of fractions $r / s$ with $s \in S$. For a module $M$, the localization $S^{-1}M$ is the module of fractions $m / s$ with $m \in M$ and $s \in S$, and it is a module over $S^{-1}R$. It keeps the part of $M$ that the elements of $S$ do not kill. Localization at a prime ideal $\mathfrak{p}$, with $S = R \setminus \mathfrak{p}$, gives the local data of $M$ at $\mathfrak{p}$. Mathlib has the construction `LocalizedModule S M` and the predicate `IsLocalizedModule S f`, which says that a linear map $f : M \to M'$ is a localization map. Most results use the predicate, so they apply to each model of the localization. This section covers both, the universal property, exactness, and the localization of submodules and quotients.

### The library around it

#### The construction

The type `LocalizedModule S M` is the quotient of $M \times S$ by the relation `LocalizedModule.r`: $(m, s) \sim (m', s')$ if $u s' m = u s m'$ for some $u \in S$. The class of $(m, s)$ is `LocalizedModule.mk m s`, read as $m / s$. The factor $u$ is needed when $M$ has elements that $S$ kills.

**Theorem.** $m / s = m' / s'$ if and only if $u s' m = u s m'$ for some $u \in S$.

*Proof.* This is the definition of the quotient by the relation, once the relation is known to be an equivalence. It is reflexive and symmetric by its form. For transitivity, let $u s' m = u s m'$ and $v s'' m' = v s' m''$. Multiply the first equation by $v s''$ and the second by $u s$; both sides then contain $u v s s'' m'$, so $(u v s') s'' m = (u v s') s m''$. $\square$

This is `LocalizedModule.mk_eq`, and `LocalizedModule.r.isEquiv` is the proof that the relation is an equivalence. The sum is $m / s + m' / s' = (s' m + s m') / (s s')$ (`LocalizedModule.mk_add_mk`), and a fraction of $R$ acts by $(r / t) (m / s) = (r m) / (t s)$ (`LocalizedModule.mk_smul_mk`). So `LocalizedModule S M` is a module over `Localization S` and over $R$. Common factors cancel: `LocalizedModule.mk_cancel` states $(s m) / (s t) = m / t$. The proofs about elements use `LocalizedModule.induction_on`.

The map $m \mapsto m / 1$ is the linear map `LocalizedModule.mkLinearMap S M`.

**Theorem.** The kernel of $M \to S^{-1}M$ is the set of $m$ with $s m = 0$ for some $s \in S$.

*Proof.* By the theorem above, $m / 1 = 0 / 1$ if and only if $u m = 0$ for some $u \in S$. $\square$

This is `LocalizedModule.mem_ker_mkLinearMap_iff`. So $S^{-1}M = 0$ if and only if each element of $M$ is killed by some element of $S$ (`LocalizedModule.subsingleton_iff`).

The special cases have their own names. For an element $f \in R$, `LocalizedModule.Away f M` is the localization at the powers of $f$, written $M_f$. For a prime ideal $\mathfrak{p}$, `LocalizedModule.AtPrime P M` is the localization $M_{\mathfrak{p}}$ at the complement of $\mathfrak{p}$.

#### The predicate and the universal property

A linear map $f : M \to M'$ is a localization at $S$, `IsLocalizedModule S f`, when three conditions hold:

| Field | Condition |
|---|---|
| `IsLocalizedModule.map_units` | each $s \in S$ acts on $M'$ as a bijection |
| `IsLocalizedModule.surj` | each $y \in M'$ has $s y = f(x)$ for some $x \in M$, $s \in S$ |
| `IsLocalizedModule.exists_of_eq` | $f(x_1) = f(x_2)$ implies $c x_1 = c x_2$ for some $c \in S$ |

The construction satisfies it, by the instance for `LocalizedModule.mkLinearMap`. In the other direction, each localization map is the construction up to a unique equivalence.

**Theorem.** If $f : M \to M'$ is a localization at $S$, then there is a linear equivalence $S^{-1}M \simeq M'$ that sends $m / s$ to $s^{-1} f(m)$.

*Proof.* Define the map by $m / s \mapsto s^{-1} f(m)$, where $s^{-1}$ is the inverse of the action of $s$ on $M'$. It is well defined: if $u s' m = u s m'$, then applying $f$ and the inverses of $u$, $s$ and $s'$ gives $s^{-1} f(m) = s'^{-1} f(m')$. It is surjective by `IsLocalizedModule.surj` and injective by `IsLocalizedModule.exists_of_eq`. $\square$

This is `IsLocalizedModule.iso`. The universal property is `IsLocalizedModule.lift`: a linear map $g : M \to M''$ into a module on which each $s \in S$ acts bijectively factors through $f$ in a unique way (`IsLocalizedModule.lift_comp`, `IsLocalizedModule.lift_unique`). Two localizations of the same module are equivalent by `IsLocalizedModule.linearEquiv`. The fraction notation for a general localization map is `IsLocalizedModule.mk' f m s`, with `IsLocalizedModule.mk'_eq_mk'_iff` and `IsLocalizedModule.mk'_surjective`. Each element has a multiple by some $s \in S$ that comes from $M$, `IsLocalizedModule.exists_integer_multiple`, and the file `Mathlib.Algebra.Module.LocalizedModule.Int` gives common denominators for finite families (`IsLocalizedModule.exist_integer_multiples_of_finset`).

The localization of the ring is a special case. For an $R$-algebra $A$, the structure map $R \to A$ is a localization of modules exactly when $A$ is a localization of rings: `isLocalizedModule_iff_isLocalization'`. The fractions agree by `IsLocalization.mk'_eq_mk'`.

For the powers of one element, `IsLocalizedModule.Away r f` has the constructor `IsLocalizedModule.Away.mk`, which asks for the three conditions with powers of $r$. It depends only on $r$ up to a unit factor (`IsLocalizedModule.Away.iff_of_associated`).

#### Maps and exactness

A linear map $g : M \to N$ gives a linear map between localizations, `IsLocalizedModule.map S f f' g`, with $f(m) \mapsto f'(g(m))$ (`IsLocalizedModule.map_comp`). For the constructions it is `LocalizedModule.map S g`, which is linear over `Localization S`. The map is functorial (`IsLocalizedModule.map_id`) and keeps injective and surjective maps (`IsLocalizedModule.map_injective`, `IsLocalizedModule.map_surjective`).

**Theorem.** Localization is exact: if $M_0 \xrightarrow{g} M_1 \xrightarrow{h} M_2$ is exact, then $S^{-1}M_0 \to S^{-1}M_1 \to S^{-1}M_2$ is exact.

*Proof.* The composition is $0$ since $h g = 0$. Let $m / s$ go to $0$ in $S^{-1}M_2$. Then $h(m) / s = 0$, so $u h(m) = 0$ for some $u \in S$. Thus $h(u m) = 0$, and $u m = g(m_0)$ by exactness. So $m / s = g(m_0) / (u s)$, which is in the image. $\square$

This is `IsLocalizedModule.map_exact`, with the form for the constructions `LocalizedModule.map_exact`. The consequences are in `Mathlib.Algebra.Module.LocalizedModule.Submodule`: the kernel and the range of the localized map are the localizations of the kernel and of the range (`LinearMap.ker_localizedMap_eq_localized₀_ker`, `LinearMap.range_localizedMap_eq_localized₀_range`). A localized map is surjective if and only if the localized cokernel is $0$ (`LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker`). Over a ring where each element of $S$ is regular on $M$, the localization map is injective (`IsLocalizedModule.injective_iff_isRegular`).

#### Submodules and quotients

A submodule $M' \le M$ gives the submodule $S^{-1}M'$ of $S^{-1}M$. For a localization map $f : M \to N$ and a localization $S^{-1}R \to A$ of rings, it is `Submodule.localized' A S f M'`, an $A$-submodule of $N$; the version over $R$ is `Submodule.localized₀`. For the constructions, `Submodule.localized p M'` is a submodule of `LocalizedModule p M`. The membership lemma `Submodule.mem_localized'` says that the elements are the fractions $f(m) / s$ with $m \in M'$.

**Theorem.** $S^{-1}M'$ is the span over $S^{-1}R$ of the image $f(M')$.

*Proof.* The span contains $f(m)$ for $m \in M'$, so it contains $s^{-1} f(m)$. Conversely, each element of $S^{-1}M'$ is of this form. $\square$

This is `Submodule.localized'_eq_span`. The localization keeps the lattice operations: `Submodule.localized'_inf`, `Submodule.localized'_iSup`, `Submodule.localized'_top`, `Submodule.localized'_bot`, and it is a frame map, `Submodule.localized'FrameHom`. It sends $I M'$ to $(S^{-1}I)(S^{-1}M')$ (`Submodule.localized'_smul`).

**Theorem.** Localization commutes with quotients: $S^{-1}M / S^{-1}M' \simeq S^{-1}(M / M')$.

*Proof.* Apply exactness to $0 \to M' \to M \to M / M' \to 0$. $\square$

This is `localizedQuotientEquiv`. The equivalence `Submodule.localizedEquiv` identifies the submodule `Submodule.localized p M'` with the localization of the module $M'$.

#### Common errors

1. Forgetting the factor $u$ in the equality of fractions. Over a module with torsion, $m / s = m' / s'$ does not imply $s' m = s m'$. Use `LocalizedModule.mk_eq`, which has the factor.
2. Proving a statement for `LocalizedModule S M` when it is needed for another model, such as `Localization S` as a module over $R$. State the result for `IsLocalizedModule S f`, and the instances give it for each model.
3. Expecting `Submodule.localized'` and `Submodule.localized₀` to be the same. The first is a submodule over the localized ring $A$, the second is the same set as a submodule over $R$; `Submodule.restrictScalars_localized'` connects them.

### Exercises

1. (A) Compute $S^{-1}(\mathbb{Z}/6)$ for $S$ the powers of $2$ in $\mathbb{Z}$.
2. (A) Show that $(\mathbb{Z}/n)_{(0)} = 0$ for $n \ne 0$, where $(0)$ is the zero prime ideal of $\mathbb{Z}$.
3. (B) Show that $S^{-1}M = 0$ for a finitely generated $M$ if and only if some $s \in S$ kills $M$.
4. (B) Show that the map $\mathbb{Z} \to \mathbb{Z}[1/2]$ satisfies the three conditions of `IsLocalizedModule` for the powers of $2$.
5. (B) Let $g : M \to N$ be a linear map. Show that $g$ is injective if $S^{-1}g$ is injective for each localization $S = R \setminus \mathfrak{m}$ at a maximal ideal $\mathfrak{m}$.
6. (C) Show that $S^{-1}(M_1 \oplus M_2) \simeq S^{-1}M_1 \oplus S^{-1}M_2$ with the universal property.

### Reference

<?reference?>
