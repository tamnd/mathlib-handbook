---
title: Solvability by radicals
kind: theory
modules:
  - Mathlib.FieldTheory.AbelRuffini
explains:
  E3: [solvableByRad, isSolvable_gal_minpoly, isSolvable_gal_of_irreducible, gal_X_pow_sub_C_isSolvable]
  E2: [solvableByRad.induction, solvableByRad.rad_mem, solvableByRad_le, solvableByRad_le_algClosure, isAlgebraic_solvableByRad, gal_mul_isSolvable, gal_prod_isSolvable, gal_isSolvable_of_splits, gal_X_pow_sub_one_isSolvable, gal_X_sub_C_isSolvable, gal_C_isSolvable, gal_X_pow_isSolvable]
  E1: auto
families: []
requires: [V11.C05, V11.C06, V05.C05, V05.C07]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Solvability by radicals

### Overview

The formulas for the roots of polynomials of degree at most $4$ use the coefficients, the field operations and square and cube roots. An element is solvable by radicals over $K$ if it can be reached from $K$ in this way. This section proves the theorem of Galois: if a root of an irreducible polynomial is solvable by radicals, then the Galois group of the polynomial is a solvable group. Since $S_5$ is not solvable, the quintic $X^5 - 4X + 2$ of Chapter 6 has roots that are not solvable by radicals over $\mathbb{Q}$. This is the theorem of Abel and Ruffini.

The section uses Chapters 5 and 6, Section 1, and from Volume 5 quotient groups (Chapter 5) and the symmetric groups (Chapter 7).

### Definitions

**Definition (Solvable group).** A group $G$ is solvable if there is a chain of subgroups $1 = G_0 \leq G_1 \leq \dots \leq G_k = G$ with $G_{i-1}$ normal in $G_i$ and $G_i/G_{i-1}$ abelian for each $i$. Equivalently, the derived series $G^{(0)} = G$, $G^{(i+1)} = [G^{(i)}, G^{(i)}]$ reaches $1$.

The forms agree, since $G_i/G_{i-1}$ is abelian exactly when $[G_i, G_i] \leq G_{i-1}$. Abelian groups are solvable, and so are the groups $S_3$ and $S_4$, with the chains $1 \leq A_3 \leq S_3$ and $1 \leq V_4 \leq A_4 \leq S_4$.

::: mathlib
`Group.IsSolvable` · `Mathlib.GroupTheory.Solvable`

The class `Group.IsSolvable G` says that some term of `derivedSeries G` is `⊥`. The closure properties are `Group.isSolvable_of_comm`, `Group.isSolvable_of_isSolvable_injective` for subgroups, `Group.isSolvable_of_surjective` for quotients, and `Group.isSolvable_of_ker_le_range` for extensions. The old name `IsSolvable` is a deprecated alias.

<?decl Group.IsSolvable?>
<?decl Group.isSolvable_of_ker_le_range?>
:::

**Definition (Solvable by radicals).** Let $E/K$ be an extension. The field of the elements of $E$ solvable by radicals over $K$ is the smallest intermediate field $R$ of $E/K$ with this property: if $x \in E$, $n \geq 1$ and $x^n \in R$, then $x \in R$.

An element $\alpha$ is in $R$ exactly when there is a tower $K = K_0 \subseteq K_1 \subseteq \dots \subseteq K_m \subseteq E$ with $\alpha \in K_m$ and $K_i = K_{i-1}(\alpha_i)$, $\alpha_i^{n_i} \in K_{i-1}$. A polynomial is solvable by radicals if its roots in a splitting field are.

::: mathlib
`solvableByRad` · `Mathlib.FieldTheory.AbelRuffini`

`solvableByRad F E : IntermediateField F E`, defined as the infimum of the intermediate fields closed under `n`th roots for `n ≠ 0`. `solvableByRad.rad_mem` is the closure property and `solvableByRad_le` the minimality. The principle `solvableByRad.induction` proves a property of each element from the base field, sums, negatives, products, inverses and roots. Each element is algebraic (`isAlgebraic_solvableByRad`, `solvableByRad_le_algClosure`). In characteristic $p$ the definition admits $p$th roots, which give purely inseparable steps; it does not admit the roots of $X^p - X - a$.

<?decl solvableByRad?>
:::

### Theorems and proofs

**Theorem ($S_n$ is not solvable).** For $n \geq 5$, the symmetric group $S_n$ is not solvable.

*Proof.* Let $H \leq S_n$ be a subgroup that contains all the $3$-cycles. For distinct $a, b, c, d, e$, which exist since $n \geq 5$, a direct computation gives
$$(a\,b\,c) = \sigma \tau \sigma^{-1} \tau^{-1}, \qquad \sigma = (a\,b\,d),\ \tau = (a\,c\,e),$$
where products are composed from right to left. So each $3$-cycle is a commutator of two $3$-cycles of $H$, and $[H, H]$ also contains all the $3$-cycles. By induction each term $S_n^{(i)}$ of the derived series contains all the $3$-cycles, so it is not trivial. $\square$

::: mathlib
`Equiv.Perm.not_isSolvable` · `Mathlib.GroupTheory.Solvable`

For `5 ≤ Cardinal.mk X`, the statement `¬Group.IsSolvable (Equiv.Perm X)`, proved with the same commutator. `Equiv.Perm.not_isSolvable_fin_5` is the case of `Fin 5`, and `Equiv.Perm.isSolvable` gives the solvability for at most four letters.

<?decl Equiv.Perm.not_isSolvable?>
:::

**Lemma (Galois groups of products and factors).** Let $f, g \in K[X]$.

1. If $\operatorname{Gal}(f)$ and $\operatorname{Gal}(g)$ are solvable, then $\operatorname{Gal}(fg)$ is solvable.
2. If $g$ splits in a splitting field $L$ of $f$ and $\operatorname{Gal}(f)$ is solvable, then $\operatorname{Gal}(g)$ is solvable.
3. For each $n$ and $a \in K$, $\operatorname{Gal}(X^n - a)$ is solvable.

*Proof.* (1) The restriction map $\operatorname{Gal}(fg) \to \operatorname{Gal}(f) \times \operatorname{Gal}(g)$ is injective (Chapter 6, Section 1), and subgroups of products of solvable groups are solvable. (2) A splitting field of $g$ is an intermediate field of $L/K$, normal over $K$, and restriction maps $\operatorname{Gal}(L/K)$ onto its group (Chapter 5, Section 1). A quotient of a solvable group is solvable. (3) Write the proof when $\operatorname{char} K \nmid n$ and $a \neq 0$. Let $L$ be a splitting field. The polynomial $X^n - a$ is separable, so it has $n$ distinct roots $\alpha = \alpha_1, \dots, \alpha_n$ in $L$, and the quotients $\alpha_i/\alpha$ are $n$ distinct $n$th roots of unity. So $\mu_n(L)$ has order $n$, and it has a generator $\zeta$, a primitive $n$th root of unity. Put $M = K(\zeta)$. Then $\operatorname{Gal}(L/M)$ is normal in $\operatorname{Gal}(L/K)$, since $M/K$ is Galois, with quotient $\operatorname{Gal}(M/K)$, which is abelian by Section 1. The group $\operatorname{Gal}(L/M)$ embeds into $\mu_n$ by $\sigma \mapsto \sigma(\alpha)/\alpha$, as in the theorem of Kummer, so it is abelian. So $1 \leq \operatorname{Gal}(L/M) \leq \operatorname{Gal}(L/K)$ is a chain with abelian quotients. $\square$

::: mathlib
`gal_X_pow_sub_C_isSolvable` · `Mathlib.FieldTheory.AbelRuffini`

For each field `F`, `n : ℕ` and `x : F`, the statement `Group.IsSolvable (X ^ n - C x).Gal`, with no hypothesis on the characteristic. The proof treats the cases `n = 0`, `x = 0` and the inseparable case separately. The other parts of the lemma are `gal_mul_isSolvable`, `gal_prod_isSolvable` and `gal_isSolvable_of_splits`, and the trivial cases are `gal_C_isSolvable`, `gal_X_sub_C_isSolvable`, `gal_X_pow_isSolvable` and `gal_X_pow_sub_one_isSolvable`.

<?decl gal_X_pow_sub_C_isSolvable?>
:::

**Theorem (Galois).** Let $E/K$ be an extension and $\alpha \in E$ solvable by radicals over $K$. Then $\operatorname{Gal}(\operatorname{minpoly}_K \alpha)$ is solvable. So if $f \in K[X]$ is irreducible and has a root solvable by radicals, then $\operatorname{Gal}(f)$ is solvable.

*Proof.* Let $S$ be the set of the $x \in E$, algebraic over $K$, such that $\operatorname{Gal}(\operatorname{minpoly}_K x)$ is solvable. It suffices to prove that $S$ is an intermediate field closed under $n$th roots, since then $S$ contains the smallest such field.

*$S$ contains $K$:* the minimal polynomial of $c \in K$ is $X - c$, with the trivial group.

*$S$ is closed under the field operations:* let $x, y \in S$ with minimal polynomials $f, g$. Let $L$ be a splitting field of $fg$ over $K$ that contains $x$ and $y$; the group $\operatorname{Gal}(fg)$ is solvable by part (1) of the lemma. The elements $x + y$, $-x$, $xy$ and $x^{-1}$ lie in $L$, and $L/K$ is normal, so their minimal polynomials split in $L$. By part (2), their groups are solvable.

*$S$ is closed under roots:* let $x \in E$ with $x^n = y \in S$, $n \geq 1$, and let $g$ be the minimal polynomial of $y$. Then $x$ is a root of $h = g(X^n) \cdot (X^n - 1)$. Let $L$ be a splitting field of $h$ over $K$ that contains $x$. The roots $y_1, \dots, y_m$ of $g$ are the $n$th powers of the roots of $g(X^n)$, so they lie in $L$, and $M = K(y_1, \dots, y_m)$ is a splitting field of $g$. Over $M$, $h = \prod_j (X^n - y_j) \cdot (X^n - 1)$, so $\operatorname{Gal}(L/M)$ is solvable by parts (1) and (3), applied over $M$. Since $M/K$ is normal, restriction maps $\operatorname{Gal}(L/K)$ onto $\operatorname{Gal}(M/K) = \operatorname{Gal}(g)$ with kernel $\operatorname{Gal}(L/M)$. An extension of a solvable group by a solvable group is solvable, so $\operatorname{Gal}(L/K)$ is solvable. The minimal polynomial of $x$ divides $h$, so it splits in $L$, and its group is solvable by part (2).

For the last statement, if $f$ is irreducible with root $\alpha$, then $f$ is $\operatorname{minpoly}_K \alpha$ up to a unit. $\square$

::: mathlib
`isSolvable_gal_minpoly` · `Mathlib.FieldTheory.AbelRuffini`

For `x ∈ solvableByRad F E`, the statement `Group.IsSolvable (minpoly F x).Gal`. The proof follows the plan above with `solvableByRad.induction`.

<?decl isSolvable_gal_minpoly?>
:::

::: mathlib
`isSolvable_gal_of_irreducible` · `Mathlib.FieldTheory.AbelRuffini`

For `x ∈ solvableByRad F E`, `Irreducible q` and `aeval x q = 0`, the statement `Group.IsSolvable q.Gal`. The docstring calls it one direction of the theorem of Abel and Ruffini. The index of this edition has no declaration for the converse, that a polynomial with a solvable group in characteristic $0$ is solvable by radicals.

<?decl isSolvable_gal_of_irreducible?>
:::

**Theorem (The converse, in characteristic $0$).** Let $\operatorname{char} K = 0$ and let $f \in K[X]$ have a solvable Galois group. Then the roots of $f$ are solvable by radicals over $K$.

*Proof.* Let $L$ be a splitting field of $f$, $n = [L:K]$, and $\zeta$ a primitive $n$th root of unity in an extension of $L$. Put $K' = K(\zeta)$ and $L' = L(\zeta)$. Then $L'/K'$ is Galois, and $\operatorname{Gal}(L'/K')$ embeds into $\operatorname{Gal}(L/K)$ by restriction, so it is solvable of order dividing $n$. Refine a chain with abelian quotients to a chain $1 = H_0 \triangleleft H_1 \triangleleft \dots \triangleleft H_k = \operatorname{Gal}(L'/K')$ with cyclic quotients of prime order; this is possible since a finite abelian group has a chain with cyclic quotients of prime order. The fixed fields $F_i = L'^{H_i}$ form a tower from $K'$ to $L'$ in which $F_{i-1}/F_i$ is Galois with cyclic group of prime order $p_i \mid n$. Since $F_i$ contains a primitive $p_i$th root of unity, a power of $\zeta$, Kummer's theorem (Section 1) gives $F_{i-1} = F_i(\beta_i)$ with $\beta_i^{p_i} \in F_i$. So $L'$ is reached from $K$ by adjoining $\zeta$, a root of $X^n - 1$, and then the radicals $\beta_i$. $\square$

### Examples

**Example (A quintic that is not solvable by radicals).** Let $f = X^5 - 4X + 2 \in \mathbb{Q}[X]$. Chapter 6, Section 2 proved that $f$ is irreducible and that $\operatorname{Gal}(f) \cong S_5$. Since $S_5$ is not solvable, no root of $f$ in $\mathbb{C}$ is solvable by radicals over $\mathbb{Q}$, by the theorem of Galois. So no formula in radicals solves all quintics over $\mathbb{Q}$. In Mathlib, the conclusion is `¬ x ∈ solvableByRad ℚ ℂ` for each root `x`, by contraposition of `isSolvable_gal_of_irreducible` and `Equiv.Perm.not_isSolvable`.

**Example (Irreducibility is needed).** Let $g = (X - 1) \cdot (X^5 - 4X + 2)$. Then $g$ has the root $1 \in \mathbb{Q}$, which is solvable by radicals. But a splitting field of $g$ is a splitting field of $X^5 - 4X + 2$, so $\operatorname{Gal}(g) \cong S_5$ is not solvable. So the theorem needs the irreducibility of $q$; it concerns the minimal polynomial of the given root, not an arbitrary polynomial with that root.

**Example (A solvable quintic).** The roots of $X^5 - 2$ over $\mathbb{Q}$ are $\zeta^i \sqrt[5]{2}$ with $\zeta = e^{2\pi i/5}$. The splitting field $\mathbb{Q}(\zeta, \sqrt[5]{2})$ has degree $20$, since $4$ and $5$ divide it and it is at most $4 \cdot 5$. Its group is the group of the maps $x \mapsto ax + b$ on $\mathbb{Z}/5\mathbb{Z}$, $a \neq 0$, with the chain $1 \leq \mathbb{Z}/5\mathbb{Z} \leq \operatorname{Gal}$ and quotient $(\mathbb{Z}/5\mathbb{Z})^\times$. It is solvable, as part (3) of the lemma says.

### The library around it

The file `Mathlib.FieldTheory.AbelRuffini` contains the definition of `solvableByRad`, the lemmas on Galois groups of products and of $X^n - a$, and the direction of the theorem proved here. The solvable groups and their closure properties are in `Mathlib.GroupTheory.Solvable`, and the simplicity of the alternating groups, which gives a second proof that $S_n$ is not solvable for $n \geq 5$, is in `Mathlib.GroupTheory.SpecificGroups.Alternating`. The reference table lists the declarations of the section.

### Exercises

1. (A) Show that the dihedral group of order $2n$ and each group of order $p^k$ are solvable.
2. (A) Solve $X^3 - 3X + 1 = 0$ by radicals with the formula of Cardano, and check that the solution needs the complex number $\zeta_3$ although all three roots are real.
3. (A) Show that $X^5 - 6X + 3$ is not solvable by radicals over $\mathbb{Q}$.
4. (B) Show that a transitive subgroup of $S_p$, $p$ prime, which is solvable has order dividing $p(p-1)$. *Hint:* the last nontrivial term of the derived series is abelian, normal and transitive, so it is generated by a $p$-cycle.
5. (B) Let $f \in \mathbb{Q}[X]$ be irreducible of prime degree $p \geq 5$ and solvable by radicals. Show with Exercise 4 that $f$ has either one real root or $p$ real roots.
6. (C) Let $K = \mathbb{C}(t_1, \dots, t_n)$ and $F = K^{S_n}$, the field of symmetric rational functions. Show that the generic polynomial $\prod (X - t_i) \in F[X]$ has group $S_n$, and deduce that the general equation of degree $n \geq 5$ is not solvable by radicals.

### Notes and history

Ruffini published a proof of the insolvability of the general quintic in 1799, with a gap. Abel gave a complete proof in 1824 and 1826. Galois found the criterion with solvable groups around 1830; his memoir was published by Liouville in 1846. Hermite solved the general quintic in 1858 with elliptic modular functions, which are not radicals.

### Reference

<?reference?>
