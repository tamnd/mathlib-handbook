---
title: Shift spaces and subshifts
kind: theory
modules:
  - Mathlib.Dynamics.SymbolicDynamics.Basic
explains:
  E3: [SymbolicDynamics.FullShift.shift, SymbolicDynamics.FullShift.cylinder, SymbolicDynamics.FullShift.Subshift, SymbolicDynamics.FullShift.Pattern, SymbolicDynamics.FullShift.Pattern.occursInAt, SymbolicDynamics.FullShift.forbidden, SymbolicDynamics.FullShift.Subshift.ofForbidden, SymbolicDynamics.FullShift.LanguageOn]
  E2: [SymbolicDynamics.FullShift.shift_apply, SymbolicDynamics.FullShift.shift_add, SymbolicDynamics.FullShift.shift_zero, SymbolicDynamics.FullShift.continuous_shift, SymbolicDynamics.FullShift.mem_cylinder, SymbolicDynamics.FullShift.cylinder_eq_set_pi, SymbolicDynamics.FullShift.isOpen_cylinder, SymbolicDynamics.FullShift.isClosed_cylinder, SymbolicDynamics.FullShift.fullShift, SymbolicDynamics.FullShift.Pattern.fromConfig, SymbolicDynamics.FullShift.Pattern.shift, SymbolicDynamics.FullShift.Pattern.occursInAt_shift, SymbolicDynamics.FullShift.occursInAt_eq_cylinder, SymbolicDynamics.FullShift.isOpen_occursInAt, SymbolicDynamics.FullShift.isClosed_occursInAt, SymbolicDynamics.FullShift.isClosed_forbidden, SymbolicDynamics.FullShift.Pattern.mapsTo_shift_forbidden, SymbolicDynamics.FullShift.languageOn_mono, SymbolicDynamics.FullShift.languageOn_union, SymbolicDynamics.FullShift.languageOn_inter_subset, SymbolicDynamics.FullShift.finite_setOfPred_pattern_support_eq]
  E1: auto
families: []
requires: [V13, V21.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Shift spaces and subshifts

### Overview

Symbolic dynamics codes the orbits of a system by sequences of symbols and studies the sequences directly. The space of all configurations $x : G \to A$, for a finite alphabet $A$ and a monoid $G$ of positions such as $\mathbb{N}$, $\mathbb{Z}$ or $\mathbb{Z}^2$, carries the shift, which moves the configuration along $G$. The closed shift invariant subsets are the subshifts, and the main way to build one is to forbid a set of finite patterns. This section develops the full shift, cylinders, patterns, subshifts given by forbidden patterns and the language of a subshift. Product topologies and Tychonoff's theorem come from Volume 13, and the invariant sets and factors from Chapter 2.

### Definitions

**Definition (Full shift).** Let $A$ be a topological space, usually finite and discrete, and $G$ an additive monoid. The *full shift* is the space $A^G$ of configurations $x : G \to A$ with the product topology. For $g \in G$, the *shift* $\sigma_g : A^G \to A^G$ is $(\sigma_g x)(h) = x(g + h)$.

**Definition (Cylinder).** For a finite set $U \subseteq G$ and $x \in A^G$, the *cylinder* $[x]_U$ is the set of $y$ with $y(i) = x(i)$ for all $i \in U$.

**Definition (Pattern).** A *pattern* is a finite set $U \subseteq G$, its *support*, with a map $p : U \to A$. The pattern $p$ *occurs in $x$ at $g$* if $x(g + h) = p(h)$ for all $h \in U$. The restriction of $x$ to $U$ is a pattern.

**Definition (Subshift).** A *subshift* is a closed set $X \subseteq A^G$ with $\sigma_g(X) \subseteq X$ for all $g$. For a set $F$ of patterns, $X_F$ is the set of configurations in which no pattern of $F$ occurs at any position. The *language* of $X$ on $U$ is the set $L_U(X)$ of restrictions to $U$ of the configurations $x \in X$.

::: mathlib
`SymbolicDynamics.FullShift.shift` · `Mathlib.Dynamics.SymbolicDynamics.Basic`

`shift g x : G → A` with `shift_apply : shift g x h = x (g + h)`, for `[AddMonoid G]`. The space is the plain function type `G → A`, with the product topology of its instance. `cylinder U x` takes `U : Finset G`, and `mem_cylinder` unfolds it; `cylinder_eq_set_pi` writes it as `Set.pi U fun i ↦ {x i}`.

<?decl SymbolicDynamics.FullShift.shift?>
:::

::: mathlib
`SymbolicDynamics.FullShift.Pattern` · `Mathlib.Dynamics.SymbolicDynamics.Basic`

A structure with `config : G → A`, `support : Finset G` and `condition : ∀ g ∉ support, config g = default`, for `[Inhabited A]`: outside its support a pattern is padded with a default letter. `p.occursInAt x g` is `∀ h ∈ p.support, x (g + h) = p.config h`. `Pattern.fromConfig x U` is the restriction of `x` to `U`, and `Pattern.shift p v` is `p` moved to `v` and padded.

<?decl SymbolicDynamics.FullShift.Pattern?>
:::

### Theorems and proofs

**Proposition (The shift).** Each $\sigma_g$ is continuous, $\sigma_0 = \mathrm{id}$ and $\sigma_{g_1 + g_2} = \sigma_{g_2} \circ \sigma_{g_1}$. So $g \mapsto \sigma_g$ is a right action of $G$; for a commutative $G$ it is also an action in the usual sense.

*Proof.* A map into a product is continuous when each coordinate is, and the coordinate $h$ of $\sigma_g$ is the coordinate projection at $g + h$. For the composition, $(\sigma_{g_2}(\sigma_{g_1}x))(h) = (\sigma_{g_1}x)(g_2 + h) = x(g_1 + g_2 + h) = (\sigma_{g_1 + g_2}x)(h)$. $\square$

::: mathlib
`SymbolicDynamics.FullShift.shift_add` · `Mathlib.Dynamics.SymbolicDynamics.Basic`

`shift (g₁ + g₂) x = shift g₂ (shift g₁ x)`: the order of the factors is reversed, which matters for a noncommutative group of positions written additively.

<?decl SymbolicDynamics.FullShift.shift_add?>
:::

**Theorem (Cylinders).** If $A$ is discrete, every cylinder is open; if $A$ is $T_1$, every cylinder is closed. For a discrete $A$, the cylinders form a base of the topology, and if $A$ is finite, $A^G$ is compact.

*Proof.* The cylinder $[x]_U$ is $\bigcap_{i \in U} \pi_i^{-1}(\{x(i)\})$, where $\pi_i$ is the projection. The intersection is finite, and $\{x(i)\}$ is open when $A$ is discrete and closed when $A$ is $T_1$. Arbitrary intersections of closed sets are closed, so finiteness is not needed for the second claim. The basic open sets of the product topology are finite intersections $\bigcap_{i \in U} \pi_i^{-1}(V_i)$, and for a discrete $A$ each one is the union of the cylinders $[x]_U$ with $x(i) \in V_i$. Compactness is Tychonoff's theorem. $\square$

**Lemma (Occurrences).** A pattern $p$ occurs in $\sigma_g x$ at $h$ if and only if it occurs in $x$ at $g + h$. If $G$ is left cancellative, the set of $x$ in which $p$ occurs at $g$ is a cylinder, on the support $g + U$.

*Proof.* The first claim is $x(g + h + u) = (\sigma_g x)(h + u)$. For the second, $p$ occurs at $g$ exactly when $x(g + u) = p(u)$ for $u \in U$, and left cancellation makes $u \mapsto g + u$ injective, so these are the conditions of one cylinder. $\square$

**Theorem (Forbidden patterns).** Let $A$ be discrete and $G$ left cancellative. For each set $F$ of patterns, $X_F$ is a subshift. Conversely, every subshift $X$ is $X_F$ for $F$ the set of patterns that occur in no configuration of $X$ at any position.

*Proof.* The complement of $X_F$ is the union over $p \in F$ and $g \in G$ of the sets where $p$ occurs at $g$. These are cylinders, so open, and $X_F$ is closed. If $x \in X_F$ and $p$ occurred in $\sigma_g x$ at $h$, then by the lemma $p$ would occur in $x$ at $g + h$; so $\sigma_g x \in X_F$.

For the converse, let $x \in X$. If $p$ occurs in $x$ at $g$, it occurs at a position of a configuration of $X$, so $p \notin F$; thus $x \in X_F$. Let $x \notin X$. Since $X$ is closed and the cylinders form a base, some cylinder $[x]_U$ is disjoint from $X$. Let $p$ be the restriction of $x$ to $U$. If $p$ occurred in some $y \in X$ at $g$, then by the lemma it would occur in $\sigma_g y \in X$ at $0$, so $\sigma_g y \in [x]_U$, a contradiction. So $p \in F$, $p$ occurs in $x$ at $0$, and $x \notin X_F$. $\square$

::: mathlib
`SymbolicDynamics.FullShift.Subshift.ofForbidden` · `Mathlib.Dynamics.SymbolicDynamics.Basic`

`Subshift A G` is a structure with `carrier`, `isClosed` and `mapsTo : ∀ g, MapsTo (shift g) carrier carrier`, and `fullShift A G` is the whole space. `Subshift.ofForbidden F` has carrier `forbidden F`, closed by `isClosed_forbidden` and invariant by `Pattern.mapsTo_shift_forbidden`. The lemma is `Pattern.occursInAt_shift` and `occursInAt_eq_cylinder`, with `isOpen_occursInAt` and `isClosed_occursInAt`. The index of this edition has no declaration for the converse, that every subshift is given by forbidden patterns.

<?decl SymbolicDynamics.FullShift.Subshift.ofForbidden?>
:::

**Proposition (Language).** The language is monotone in $X$ and $L_U(X \cup Y) = L_U(X) \cup L_U(Y)$, but $L_U(X \cap Y)$ can be smaller than $L_U(X) \cap L_U(Y)$. If $A$ is finite, $L_U(X)$ is finite.

*Proof.* A restriction of a configuration of $X \cup Y$ is a restriction of a configuration of $X$ or of $Y$. For the inequality, let $X = \{x\}$ and $Y = \{y\}$ with $x \neq y$ and $x|_U = y|_U$; then $X \cap Y = \emptyset$ has empty language, but $x|_U$ lies in both languages. There are at most $|A|^{|U|}$ maps $U \to A$. $\square$

::: mathlib
`SymbolicDynamics.FullShift.LanguageOn` · `Mathlib.Dynamics.SymbolicDynamics.Basic`

`LanguageOn X U` for `X : Set (G → A)` and `U : Finset G`, with `languageOn_mono`, `languageOn_union` and `languageOn_inter_subset`, which is only an inclusion. The finiteness of the patterns with a given support is `finite_setOfPred_pattern_support_eq` for `[Finite A]`.

<?decl SymbolicDynamics.FullShift.LanguageOn?>
:::

All the definitions have multiplicative forms for a monoid written multiplicatively: `mulShift`, `MulSubshift`, `mulForbidden` and `MulSubshift.ofForbidden`.

### Examples

**Example (The golden mean shift).** Let $A = \{0, 1\}$, $G = \mathbb{Z}$ and $F = \{11\}$, the pattern with support $\{0, 1\}$ and both values $1$. Then $X_F$ is the set of sequences with no two adjacent $1$s. Let $a_n$ be the number of words of length $n$ with no $11$. A word of length $n$ that ends in $0$ is any allowed word of length $n - 1$ followed by $0$; one that ends in $1$ is an allowed word of length $n - 2$ followed by $01$. So $a_n = a_{n-1} + a_{n-2}$, with $a_1 = 2$ and $a_2 = 3$, and $a_n$ is the Fibonacci number $F_{n+2}$. Each allowed word extends by zeros to a configuration of $X_F$, so $a_n = |L_U(X_F)|$ for $U = \{0, \ldots, n - 1\}$. So $a_n$ grows like $\varphi^n$ with $\varphi = (1 + \sqrt 5)/2$, and the entropy of Chapter 7 is $\log \varphi$.

**Example (The doubling map as a factor).** On the one-sided shift $\{0, 1\}^{\mathbb{N}}$, put $\pi(x) = \sum_{k \ge 0} x(k)\, 2^{-k-1}$ modulo $1$. The map $\pi$ is continuous, since a cylinder on $\{0, \ldots, n - 1\}$ fixes $\pi(x)$ up to $2^{-n}$, and surjective, by binary expansion. It satisfies
$$\pi(\sigma_1 x) = \sum_{k \ge 0} x(k + 1)\, 2^{-k-1} = 2\pi(x) - x(0) \equiv 2\pi(x),$$
so it is a semiconjugacy from the shift to the doubling map of Section 1, in the sense of Chapter 2. It is not injective at the dyadic rationals, where $0111\ldots$ and $1000\ldots$ have the same image.

### The library around it

The module defines no sliding block codes and no shifts of finite type as a separate notion. Chapter 7 treats topological entropy in general.

Common errors of a learner:

- `shift` is a right action: `shift (g₁ + g₂) = shift g₂ ∘ shift g₁`.
- `Pattern` needs `[Inhabited A]` for the padding, and two patterns with the same values on the support but different `support` fields are different.
- `Subshift.ofForbidden` needs `[DiscreteTopology A]`; with another topology on `A` the occurrence sets need not be open.

### Exercises

1. (A) Show that the full shift $\{0, 1\}^{\mathbb{Z}}$ with $\sigma_1$ has exactly $2^n$ points with $\sigma_n x = x$.
2. (A) Show that the set of sequences in $\{0, 1\}^{\mathbb{Z}}$ with at most one $1$ is a subshift, and find a set $F$ of forbidden patterns for it. Show that no finite $F$ works.
3. (B) Show that the full shift $\{0, 1\}^{\mathbb{Z}}$ is topologically transitive under $\sigma_1$, and write down a point with a dense orbit. Hint: two cylinders on $\{-n, \ldots, n\}$ meet after a shift by $2n + 1$.
4. (B) Show that the golden mean shift is transitive, and that it is not minimal.
5. (B) For $G = \mathbb{Z}$ and a metric $d(x, y) = 2^{-n}$, where $n$ is the least $|k|$ with $x(k) \neq y(k)$, show that $d$ is a metric that gives the product topology on $A^{\mathbb{Z}}$.
6. (C) Show that a configuration of $\{0, 1\}^{\mathbb{Z}^2}$ that is invariant under $\sigma_{(1, 0)}$ and $\sigma_{(0, 1)}$ is constant, and find all configurations invariant under $\sigma_{(2, 0)}$ and $\sigma_{(0, 3)}$.

### Notes and history

Hadamard used sequences of symbols to code geodesics in 1898, and Morse and Hedlund named and developed symbolic dynamics in two papers of 1938 and 1940.

### Reference

<?reference?>
