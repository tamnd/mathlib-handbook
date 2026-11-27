---
title: Modules, vector spaces and submodules
kind: theory
modules:
  - Mathlib.Algebra.Module.Defs
  - Mathlib.Algebra.Module.Submodule.Defs
  - Mathlib.LinearAlgebra.Span.Defs
  - Mathlib.Algebra.Module.Submodule.Lattice
explains:
  E3: [Module, Submodule, Submodule.span]
  E2: [add_smul, neg_smul, Submodule.span_le, Submodule.mem_span_pair, Submodule.mem_sup, Submodule.span_induction, Submodule.mem_span_singleton]
  E1: auto
families: []
requires: [V05, V04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Modules, vector spaces and submodules

### Overview

Linear algebra studies sets where vectors add and scalars multiply them. The plane $\mathbb{R}^2$, the space of polynomials, the space of solutions of a linear differential equation and the abelian group $\mathbb{Z}/6$ all have this form. In the first three examples the scalars are the elements of a field. In the last one the scalars are the integers, and the integers do not form a field. A module is the common frame: an abelian group $M$ with an action of a ring $R$ that obeys four laws. A vector space is a module over a field.

This section gives the axioms and their first consequences. It then defines submodules, the span of a set and the lattice of submodules, with the sum and the intersection. Mathlib uses one class `Module` for all rings, and the theorems that need a field say so with a hypothesis. The section follows this choice. It states each fact for a ring $R$ and marks the facts that need more.

### Definitions

**Definition (Module).** Let $R$ be a ring. A (left) module over $R$ is an abelian group $(M, +, 0)$ with a map $R \times M \to M$, $(r, x) \mapsto r \cdot x$, such that for all $r, s \in R$ and $x, y \in M$:

1. $1 \cdot x = x$;
2. $(r s) \cdot x = r \cdot (s \cdot x)$;
3. $r \cdot (x + y) = r \cdot x + r \cdot y$;
4. $(r + s) \cdot x = r \cdot x + s \cdot x$.

The elements of $R$ are the scalars. When $R$ is a field $K$, a module over $K$ is a vector space over $K$, and its elements are vectors.

::: mathlib
`Module` · `Mathlib.Algebra.Module.Defs`

The class `Module R M` takes a semiring `R` and a commutative additive monoid `M`. It extends `DistribMulAction R M`, which gives the laws 1 to 3 and the law $r \cdot 0 = 0$, and it adds `add_smul` and `zero_smul`. The scalar action is the notation `r • x`, typed `\smul`. Mathlib does not ask for an additive group in the class, so the same class covers modules over $\mathbb{N}$, such as the natural numbers themselves. For vector spaces, write `[Field K] [AddCommGroup V] [Module K V]`. There is no class `VectorSpace`.

<?decl Module?>
:::

The axioms ask for $(r + s) \cdot x = r \cdot x + s \cdot x$, so the map $r \mapsto r \cdot x$ is additive. The axiom 3 makes the map $x \mapsto r \cdot x$ additive.

::: mathlib
`add_smul` · `Mathlib.Algebra.Module.Defs`

The law `(r + s) • x = r • x + s • x`. It is a field of the class, and the simplifier uses it in the form of this lemma. The other law, `smul_add`, comes from the class `DistribMulAction`.

<?decl add_smul?>
:::

**Definition (Submodule).** A submodule of an $R$-module $M$ is a subset $N \subseteq M$ such that $0 \in N$, $x + y \in N$ for $x, y \in N$, and $r \cdot x \in N$ for $r \in R$ and $x \in N$. A submodule of a vector space is a subspace.

A submodule is a module with the restricted operations. The axioms hold in $N$ because they hold in $M$.

::: mathlib
`Submodule` · `Mathlib.Algebra.Module.Submodule.Defs`

The type `Submodule R M` is a structure: a set `carrier` with the proofs `zero_mem'`, `add_mem'` and `smul_mem'`. The coercion `(N : Set M)` gives the set, and `x ∈ N` is membership. The type `↥N` is the subtype of the elements of `N`, and Mathlib gives it an instance of `Module R ↥N`. Two submodules with the same elements are equal by `Submodule.ext`. The lemmas `Submodule.zero_mem`, `Submodule.add_mem` and `Submodule.smul_mem` give the three closure laws in use.

<?decl Submodule?>
:::

**Definition (Span).** Let $S \subseteq M$. The span of $S$ is the intersection of all the submodules of $M$ that contain $S$. It is written $\operatorname{span}_R S$ or $\langle S \rangle$. For one vector, write $R x = \operatorname{span}_R \{x\}$.

The intersection of a family of submodules is a submodule, since each closure law passes to the intersection. So $\operatorname{span}_R S$ is a submodule, and it is the smallest submodule that contains $S$.

::: mathlib
`Submodule.span` · `Mathlib.LinearAlgebra.Span.Defs`

The span `Submodule.span R s` of a set `s : Set M`. The ring `R` is explicit, because the same abelian group can be a module over many rings: a complex vector space is also a real one. The notation `R ∙ x` is the span of the singleton `{x}`. The definition is the infimum of all the submodules that contain `s`, as on paper.

<?decl Submodule.span?>
:::

**Definition (Sum and intersection).** For submodules $N_1, N_2$ of $M$, the intersection $N_1 \cap N_2$ is a submodule. The sum is $N_1 + N_2 = \{x_1 + x_2 : x_1 \in N_1, x_2 \in N_2\}$. The submodules of $M$, ordered by inclusion, form a complete lattice. The meet is the intersection and the join is the sum. The least element is $0 = \{0\}$ and the greatest is $M$.

In Mathlib, the sum is written `N₁ ⊔ N₂` and the intersection `N₁ ⊓ N₂`. The zero submodule is `⊥` and the whole module is `⊤`.

### Theorems and proofs

**Theorem (Rules of signs).** In an $R$-module $M$, for $r \in R$ and $x \in M$: $0 \cdot x = 0$, $r \cdot 0 = 0$, $(-r) \cdot x = -(r \cdot x)$ and $(-1) \cdot x = -x$.

*Proof.* By axiom 4, $0 \cdot x = (0 + 0) \cdot x = 0 \cdot x + 0 \cdot x$. Subtract $0 \cdot x$ from both sides: $0 = 0 \cdot x$. By axiom 3, $r \cdot 0 = r \cdot (0 + 0) = r \cdot 0 + r \cdot 0$, and the same step gives $r \cdot 0 = 0$. For the third rule, axiom 4 and the first rule give $r \cdot x + (-r) \cdot x = (r + (-r)) \cdot x = 0 \cdot x = 0$. So $(-r) \cdot x$ is the additive inverse of $r \cdot x$. The fourth rule is the third one with $r = 1$, together with axiom 1. $\square$

::: mathlib
`neg_smul` · `Mathlib.Algebra.Module.Defs`

The rule `-r • x = -(r • x)` for a ring `R` and an additive group `M`. The other rules are `zero_smul`, `smul_zero` and `neg_one_smul`. These names follow the convention of Mathlib: the name reads the left side of the equation.

<?decl neg_smul?>
:::

**Theorem (Universal property of the span).** For $S \subseteq M$ and a submodule $N$ of $M$, $\operatorname{span}_R S \subseteq N$ if and only if $S \subseteq N$.

*Proof.* If $\operatorname{span}_R S \subseteq N$, then $S \subseteq \operatorname{span}_R S \subseteq N$, because $S$ is in each submodule of the intersection. Conversely, if $S \subseteq N$, then $N$ is one of the submodules in the intersection that defines the span, so the intersection is contained in $N$. $\square$

::: mathlib
`Submodule.span_le` · `Mathlib.LinearAlgebra.Span.Defs`

The statement `span R s ≤ p ↔ s ⊆ p`. It says that `span R` is the left adjoint of the coercion from submodules to sets: the two form a Galois insertion. Use `span_le.mpr` to prove that a span is small: check the generators only.

<?decl Submodule.span_le?>
:::

**Theorem (Span as linear combinations).** The span of $S$ is the set of the finite linear combinations $r_1 x_1 + \dots + r_n x_n$ with $n \ge 0$, $r_i \in R$ and $x_i \in S$. The empty combination, with $n = 0$, is $0$.

*Proof.* Let $L$ be the set of these combinations. First, $L$ is a submodule. It contains the empty sum $0$. The sum of two combinations is a combination: join the two lists. The product $r \cdot (r_1 x_1 + \dots + r_n x_n)$ is $(r r_1) x_1 + \dots + (r r_n) x_n$, by axioms 3 and 2. Next, $L$ contains $S$, since $x = 1 \cdot x$ by axiom 1. So $\operatorname{span}_R S \subseteq L$ by the universal property. Last, each submodule $N$ that contains $S$ contains each $r_i x_i$ and their sum, so $L \subseteq N$. Take the intersection over all such $N$: $L \subseteq \operatorname{span}_R S$. $\square$

For one or two vectors this gives explicit forms: $x \in R y$ if and only if $x = a y$ for some $a \in R$, and $z \in \operatorname{span}\{x, y\}$ if and only if $z = a x + b y$ for some $a, b \in R$.

::: mathlib
`Submodule.mem_span_singleton` · `Mathlib.LinearAlgebra.Span.Defs`

The statement `x ∈ R ∙ y ↔ ∃ a, a • y = x`. Note the order: the witness `a` comes first and the equation ends with `x`.

<?decl Submodule.mem_span_singleton?>
:::

::: mathlib
`Submodule.mem_span_pair` · `Mathlib.LinearAlgebra.Span.Defs`

The statement `z ∈ span R {x, y} ↔ ∃ a b, a • x + b • y = z`. For more vectors, `Submodule.mem_span_finset` and `Submodule.mem_span_set` give the general linear combination with a finitely supported family of coefficients.

<?decl Submodule.mem_span_pair?>
:::

**Theorem (Induction on the span).** Let $P$ be a property of the elements of $M$. Suppose that $P(x)$ holds for each $x \in S$, that $P(0)$ holds, that $P(x)$ and $P(y)$ give $P(x + y)$, and that $P(x)$ gives $P(r \cdot x)$. Then $P$ holds on all of $\operatorname{span}_R S$.

*Proof.* The set $N = \{x \in M : P(x)\}$ is a submodule by the last three hypotheses, and it contains $S$ by the first one. By the universal property, $\operatorname{span}_R S \subseteq N$. $\square$

::: mathlib
`Submodule.span_induction` · `Mathlib.LinearAlgebra.Span.Defs`

The induction principle on the span. The property `p` may depend on the proof `x ∈ span R s`, which makes the principle usable in more cases. In a tactic proof, write `induction hx using Submodule.span_induction with ...` and give the four cases `mem`, `zero`, `add` and `smul`.

<?decl Submodule.span_induction?>
:::

**Theorem (Sum and intersection).** For submodules $N_1, N_2$ of $M$: $x \in N_1 + N_2$ if and only if $x = y + z$ with $y \in N_1$ and $z \in N_2$; and $x \in N_1 \cap N_2$ if and only if $x \in N_1$ and $x \in N_2$. The sum $N_1 + N_2$ is the span of $N_1 \cup N_2$, and it is the least submodule that contains $N_1$ and $N_2$.

*Proof.* The set $T = \{y + z : y \in N_1, z \in N_2\}$ is a submodule: $0 = 0 + 0$, $(y + z) + (y' + z') = (y + y') + (z + z')$ and $r(y + z) = r y + r z$. It contains $N_1$, since $y = y + 0$, and $N_2$ in the same way. Each submodule that contains $N_1$ and $N_2$ contains all the sums $y + z$. So $T$ is the least submodule that contains $N_1 \cup N_2$, and this is the span of $N_1 \cup N_2$. The statement on the intersection is the definition of the intersection of two sets. $\square$

::: mathlib
`Submodule.mem_sup` · `Mathlib.LinearAlgebra.Span.Defs`

The statement `x ∈ p ⊔ p' ↔ ∃ y ∈ p, ∃ z ∈ p', y + z = x`. The join `⊔` in the lattice `Submodule R M` is the sum of submodules. The lemma `Submodule.span_union` gives `span R (s ∪ t) = span R s ⊔ span R t`.

<?decl Submodule.mem_sup?>
:::

### Examples

**Example (Coordinate spaces).** For a ring $R$ and $n \ge 1$, the set $R^n$ of the columns $(x_1, \dots, x_n)$ is an $R$-module with the operations by coordinates: $(x_i) + (y_i) = (x_i + y_i)$ and $r \cdot (x_i) = (r x_i)$. Each axiom reduces to an axiom of the ring in each coordinate. For example, axiom 2 reads $(r s) x_i = r (s x_i)$, the associativity of the product in $R$. In Mathlib this module is `Fin n → R`, with the instance `Pi.module`.

**Example (Abelian groups).** Each abelian group $A$ is a $\mathbb{Z}$-module in exactly one way. For $n \ge 0$, put $n \cdot a = a + \dots + a$ with $n$ terms, and put $(-n) \cdot a = -(n \cdot a)$. The four axioms are the laws of the multiples in Volume 5. The action is unique: axiom 1 fixes $1 \cdot a = a$, axiom 4 then fixes $n \cdot a$ for $n \ge 0$, and the rules of signs fix it for $n < 0$. So the theory of $\mathbb{Z}$-modules is the theory of abelian groups. The group $\mathbb{Z}/6$ is a $\mathbb{Z}$-module, and $6 \cdot x = 0$ for each $x$. So in a module $r \cdot x = 0$ can hold with $r \neq 0$ and $x \neq 0$. This does not happen in a vector space: if $r \neq 0$ in a field, then $x = r^{-1} \cdot (r \cdot x) = r^{-1} \cdot 0 = 0$.

**Example (A span in $\mathbb{Q}^3$).** Let $u = (1, 2, 0)$ and $v = (0, 1, 1)$ in $\mathbb{Q}^3$. The vector $w = (2, 1, -3)$ is in $\operatorname{span}\{u, v\}$: solve $a u + b v = w$. The first coordinate gives $a = 2$. The third gives $b = -3$. The second coordinate then reads $2 a + b = 4 - 3 = 1$, and this agrees with $w_2 = 1$. So $w = 2u - 3v$. The vector $e_1 = (1, 0, 0)$ is not in the span: $a = 1$ and $b = 0$ are forced by the first and the third coordinates, and then the second coordinate is $2 \neq 0$.

**Example (Sum and intersection of two planes).** In $\mathbb{R}^3$, let $N_1 = \{x : x_3 = 0\}$ and $N_2 = \{x : x_1 = 0\}$. Their intersection is $\{x : x_1 = x_3 = 0\} = \mathbb{R} e_2$. Their sum is $\mathbb{R}^3$: each vector splits as $(x_1, x_2, x_3) = (x_1, x_2, 0) + (0, 0, x_3)$. The split is not unique, since $(0, x_2, 0)$ can go to either part. The two planes meet in a line, and this measures the lack of uniqueness. Chapter 2 makes this precise with the formula $\dim(N_1 + N_2) + \dim(N_1 \cap N_2) = \dim N_1 + \dim N_2$, here $3 + 1 = 2 + 2$.

**Counterexample (The union of two lines).** In $\mathbb{R}^2$ the union $\mathbb{R} e_1 \cup \mathbb{R} e_2$ of the two axes is not a submodule. It contains $e_1$ and $e_2$, but not $e_1 + e_2 = (1, 1)$. A union of two submodules is a submodule only if one contains the other. Exercise 4 asks for the proof.

**Example (Ideals).** A ring $R$ is a module over itself, with the product as the action. Its submodules are exactly the left ideals. Over $\mathbb{Z}$, the submodules of $\mathbb{Z}$ are the sets $n \mathbb{Z}$. The span of $\{4, 6\}$ is $2 \mathbb{Z}$: it contains $6 - 4 = 2$, and each $4a + 6b$ is even. In Mathlib, `Ideal R` is defined as `Submodule R R`.

### The library around it

The class `Module` is in `Mathlib.Algebra.Module.Defs`, with the basic laws `smul_add`, `add_smul`, `mul_smul`, `one_smul`, `zero_smul` and `smul_zero`. Submodules are in `Mathlib.Algebra.Module.Submodule.Defs`, and their lattice structure is in `Mathlib.Algebra.Module.Submodule.Lattice`. The span and the formulas for the sum are in `Mathlib.LinearAlgebra.Span.Defs`. The fact that a vector space has no torsion is the class `NoZeroSMulDivisors`, with the lemma `smul_eq_zero : c • x = 0 ↔ c = 0 ∨ x = 0`.

Mathlib uses one class for many cases. A module over a semiring covers the commutative monoids with an action of $\mathbb{N}$. A field gives a vector space. A normed space, an algebra and a Lie module all extend or use `Module`. A learner who searches for a lemma on vector spaces finds it stated for a `Module` over a `DivisionRing` or a `Field`.

### Exercises

1. (A) Prove from the axioms that $r \cdot (x - y) = r \cdot x - r \cdot y$.
2. (A) Decide if $(1, 1, 1)$ is in the span of $(1, 0, 1)$ and $(0, 1, 0)$ in $\mathbb{Q}^3$. Then decide if $(1, 2, 3)$ is. Hint: solve for the coefficients from the first two coordinates, then check the third.
3. (A) Find a generator of the submodule $\operatorname{span}\{12, 18, 27\}$ of $\mathbb{Z}$. Hint: the span of a set of integers is $d \mathbb{Z}$ with $d$ the gcd.
4. (B) Let $N_1, N_2$ be submodules of $M$. Prove that $N_1 \cup N_2$ is a submodule if and only if $N_1 \subseteq N_2$ or $N_2 \subseteq N_1$. Hint: if $x \in N_1 \setminus N_2$ and $y \in N_2 \setminus N_1$, look at $x + y$.
5. (B) Prove that there is no $\mathbb{Q}$-module structure on $\mathbb{Z}/6$. Hint: compute $6 \cdot ((1/6) \cdot x)$ in two ways.
6. (B) Prove the modular law: if $N_1 \subseteq N_3$, then $N_1 + (N_2 \cap N_3) = (N_1 + N_2) \cap N_3$. Hint: write an element of the right side as $y + z$ and show that $z \in N_3$.
7. (B) Let $V$ be the real vector space of the functions $\mathbb{R} \to \mathbb{R}$. Show that the even functions and the odd functions form two subspaces $E$ and $O$ with $E \cap O = 0$ and $E + O = V$. Hint: $f(x) = \frac{f(x) + f(-x)}{2} + \frac{f(x) - f(-x)}{2}$.
8. (C) Let $M$ be an abelian group and $n \ge 1$. Show that $M$ has a $\mathbb{Z}/n$-module structure if and only if $n x = 0$ for each $x \in M$, and that this structure is then unique. Hint: the action of the class of $k$ must be the action of $k \in \mathbb{Z}$.

### Notes and history

The axioms of a vector space appear first in the "Calcolo geometrico" of Giuseppe Peano in 1888, after the work of Grassmann on extension theory in 1844. Modules over rings arose in the work of Dedekind on ideals in number fields and of Emmy Noether in the 1920s, who saw that the theory of ideals and the theory of abelian groups with operators fit in one frame. The word "module" in this sense comes from Dedekind's "Modul".

The choice to define `Module` over a semiring, and not to define a separate class for vector spaces, keeps one library of lemmas for all cases. The cost is that a learner must add the hypothesis `Field K` when a theorem needs division.

### Reference

<?reference?>
