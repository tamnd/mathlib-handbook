---
title: Linear maps, kernels and ranges
kind: theory
modules:
  - Mathlib.Algebra.Module.LinearMap.Defs
  - Mathlib.Algebra.Module.Submodule.Ker
  - Mathlib.Algebra.Module.Submodule.Range
  - Mathlib.Algebra.Module.Equiv.Defs
  - Mathlib.Algebra.Module.LinearMap.End
explains:
  E3: [LinearMap, LinearMap.ker, LinearMap.range, LinearEquiv]
  E2: [LinearMap.map_add, LinearMap.ext, LinearMap.comp, LinearMap.mem_ker, LinearMap.ker_eq_bot, Module.End, Module.End.mul_eq_comp]
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

## Linear maps, kernels and ranges

### Overview

A linear map is a map between modules that respects the sum and the scalar action. Linear maps are the morphisms of linear algebra, in the way that homomorphisms are the morphisms of group theory. Rotations of the plane, the derivative of polynomials, the evaluation of a function at a point and the product by a matrix are linear maps. Each linear map has a kernel, the vectors that it sends to $0$, and a range, the vectors that it reaches. The kernel measures the failure of injectivity, and the range measures the failure of surjectivity. A linear map that is bijective is a linear equivalence, and its inverse is again linear.

This section defines these objects, proves their basic properties, and introduces the ring $\operatorname{End}_R(M)$ of the linear maps from $M$ to itself. The ring of endomorphisms is the home of the eigenvalues and of the characteristic polynomial in Chapter 5.

### Definitions

**Definition (Linear map).** Let $M$ and $N$ be modules over a ring $R$. A map $f : M \to N$ is linear if $f(x + y) = f(x) + f(y)$ and $f(r \cdot x) = r \cdot f(x)$ for all $x, y \in M$ and $r \in R$. The set of linear maps is written $\operatorname{Hom}_R(M, N)$.

::: mathlib
`LinearMap` · `Mathlib.Algebra.Module.LinearMap.Defs`

A linear map is a structure that bundles the function with the two laws. The notation is `M →ₗ[R] N`. The general form `M →ₛₗ[σ] N` is semilinear: it takes a ring map `σ : R →+* S` and asks `f (r • x) = σ r • f x`. A conjugate linear map of complex spaces is the case where `σ` is the complex conjugation. A linear map is the case `σ = RingHom.id R`. A linear map coerces to a function, so `f x` is the value at `x`.

<?decl LinearMap?>
:::

::: mathlib
`LinearMap.map_add` · `Mathlib.Algebra.Module.LinearMap.Defs`

The law `f (x + y) = f x + f y`. The general lemma `map_add` for each class of additive maps does the same job and is the form that the simplifier prefers.

<?decl LinearMap.map_add?>
:::

**Definition (Kernel and range).** The kernel of $f$ is $\ker f = \{x \in M : f(x) = 0\}$. The range of $f$ is $\operatorname{im} f = \{f(x) : x \in M\}$.

::: mathlib
`LinearMap.ker` · `Mathlib.Algebra.Module.Submodule.Ker`

The kernel `LinearMap.ker f` as a `Submodule R M`, so dot notation gives `f.ker`. It is defined as the preimage `comap f ⊥`. The membership lemma `LinearMap.mem_ker` unfolds it.

<?decl LinearMap.ker?>
:::

::: mathlib
`LinearMap.range` · `Mathlib.Algebra.Module.Submodule.Range`

The range `LinearMap.range f` as a `Submodule R N`. It is the image `map f ⊤` of the whole module.

<?decl LinearMap.range?>
:::

**Definition (Linear equivalence).** A linear equivalence $M \cong N$ is a bijective linear map. Two modules are isomorphic if there is a linear equivalence between them.

::: mathlib
`LinearEquiv` · `Mathlib.Algebra.Module.Equiv.Defs`

The type `M ≃ₗ[R] N` bundles a linear map `toFun` with an inverse function `invFun` and the two proofs that they are inverse. The inverse is `e.symm`, of type `N ≃ₗ[R] M`, and the composition is `e.trans e'`. Mathlib stores the inverse as data so that it is computable and has a clear definition. From a bijective linear map, `LinearEquiv.ofBijective` builds the equivalence.

<?decl LinearEquiv?>
:::

**Definition (Endomorphism).** An endomorphism of $M$ is a linear map $M \to M$. The set $\operatorname{End}_R(M)$ is a ring: the sum is pointwise, the product is the composition $f g = f \circ g$, and the unit is the identity.

::: mathlib
`Module.End` · `Mathlib.Algebra.Module.LinearMap.End`

The type `Module.End R M` is `M →ₗ[R] M`, with the ring structure of composition. When `R` is commutative, it is an `R`-algebra, so a polynomial can be evaluated at an endomorphism. This is the use in Chapter 5.

<?decl Module.End?>
:::

::: mathlib
`Module.End.mul_eq_comp` · `Mathlib.Algebra.Module.LinearMap.End`

The statement `f * g = f ∘ₗ g`: the product in the ring is the composition, and it applies `g` first. So `(f * g) x = f (g x)`, and this holds by `rfl`. The power `f ^ n` is the `n`-fold composition.

<?decl Module.End.mul_eq_comp?>
:::

### Theorems and proofs

**Theorem (Basic properties).** Let $f : M \to N$ be linear. Then $f(0) = 0$, $f(-x) = -f(x)$, and $f(r_1 x_1 + \dots + r_n x_n) = r_1 f(x_1) + \dots + r_n f(x_n)$.

*Proof.* The scalar law with $r = 0$ gives $f(0) = f(0 \cdot 0) = 0 \cdot f(0) = 0$. With $r = -1$ it gives $f(-x) = f((-1) \cdot x) = (-1) \cdot f(x) = -f(x)$, by the rules of signs of Section 1. The formula for combinations follows from the two laws by induction on $n$. $\square$

**Theorem (Extensionality).** Two linear maps $f, g : M \to N$ are equal if $f(x) = g(x)$ for each $x \in M$. If $M = \operatorname{span}_R S$, then $f = g$ as soon as $f(s) = g(s)$ for each $s \in S$.

*Proof.* The first statement says that a linear map is determined by its function, which is the definition. For the second one, the set $\{x : f(x) = g(x)\}$ is a submodule: it is the kernel of $f - g$, and the next theorem shows that a kernel is a submodule. It contains $S$, so it contains $\operatorname{span}_R S = M$. $\square$

::: mathlib
`LinearMap.ext` · `Mathlib.Algebra.Module.LinearMap.Defs`

Two linear maps are equal if they agree at each point: `(∀ x, f x = g x) → f = g`. The tactic `ext x` applies this lemma. For maps out of a span, `LinearMap.ext_on` checks the generators only. For maps out of `R^n` or out of a module with a basis, Mathlib has `ext` lemmas that reduce to the basis vectors.

<?decl LinearMap.ext?>
:::

**Theorem (Kernel and range are submodules).** For a linear map $f : M \to N$, $\ker f$ is a submodule of $M$ and $\operatorname{im} f$ is a submodule of $N$.

*Proof.* $f(0) = 0$, so $0 \in \ker f$. If $f(x) = f(y) = 0$, then $f(x + y) = 0 + 0 = 0$ and $f(r x) = r \cdot 0 = 0$. For the range, $0 = f(0)$. Also $f(x) + f(y) = f(x + y)$ and $r f(x) = f(r x)$, and both lie in the range. $\square$

::: mathlib
`LinearMap.mem_ker` · `Mathlib.Algebra.Module.Submodule.Ker`

The statement `y ∈ ker f ↔ f y = 0`. It is a `simp` lemma.

<?decl LinearMap.mem_ker?>
:::

**Theorem (Injectivity and the kernel).** Let $M, N$ be modules over a ring. A linear map $f : M \to N$ is injective if and only if $\ker f = 0$. It is surjective if and only if $\operatorname{im} f = N$.

*Proof.* If $f$ is injective and $f(x) = 0 = f(0)$, then $x = 0$, so $\ker f = 0$. Conversely, let $\ker f = 0$ and $f(x) = f(y)$. Then $f(x - y) = f(x) - f(y) = 0$, so $x - y \in \ker f = 0$, and $x = y$. The statement on surjectivity is the definition of the range. $\square$

The proof uses subtraction, so it needs additive groups. Over a semiring, such as $\mathbb{N}$, the kernel can be zero for a map that is not injective. Exercise 8 gives such a map.

::: mathlib
`LinearMap.ker_eq_bot` · `Mathlib.Algebra.Module.Submodule.Ker`

The statement `ker f = ⊥ ↔ Function.Injective f`, for modules over a ring. The zero submodule is written `⊥`. The direction to the right is the usual way to prove injectivity: show that `f x = 0` forces `x = 0`.

<?decl LinearMap.ker_eq_bot?>
:::

**Theorem (Composition and inverse).** The composition of two linear maps is linear. If $f : M \to N$ is a bijective linear map, then the inverse map $f^{-1} : N \to M$ is linear.

*Proof.* For $g \circ f$: $g(f(x + y)) = g(f(x) + f(y)) = g(f(x)) + g(f(y))$, and $g(f(r x)) = g(r f(x)) = r g(f(x))$. For the inverse, let $u, v \in N$ and put $x = f^{-1}(u)$ and $y = f^{-1}(v)$. Then $f(x + y) = u + v$, so $f^{-1}(u + v) = x + y = f^{-1}(u) + f^{-1}(v)$. In the same way $f(r x) = r u$ gives $f^{-1}(r u) = r f^{-1}(u)$. $\square$

::: mathlib
`LinearMap.comp` · `Mathlib.Algebra.Module.LinearMap.Defs`

The composition `g.comp f`, also written `g ∘ₗ f`. It applies `f` first. For endomorphisms, `g * f` is the same map, but the two forms are not syntactically equal, and a proof can need `Module.End.mul_eq_comp` of the box above to pass from one to the other.

<?decl LinearMap.comp?>
:::

**Theorem (Images and preimages).** Let $f : M \to N$ be linear. If $M_0$ is a submodule of $M$, then $f(M_0)$ is a submodule of $N$. If $N_0$ is a submodule of $N$, then $f^{-1}(N_0)$ is a submodule of $M$ that contains $\ker f$. For a set $S \subseteq M$, $f(\operatorname{span} S) = \operatorname{span} f(S)$.

*Proof.* The first two statements follow from the laws of $f$ as in the theorem on kernels. The preimage of $N_0$ contains $f^{-1}(0) = \ker f$, since $0 \in N_0$. For the last statement, $f(\operatorname{span} S)$ is a submodule that contains $f(S)$, so it contains $\operatorname{span} f(S)$. Conversely, an element of $f(\operatorname{span} S)$ is $f(r_1 s_1 + \dots + r_n s_n) = r_1 f(s_1) + \dots + r_n f(s_n)$, a combination of elements of $f(S)$. $\square$

In Mathlib the image is `Submodule.map f M₀` and the preimage is `Submodule.comap f N₀`.

### Examples

**Example (A map from $\mathbb{R}^3$ to $\mathbb{R}^2$).** Let $f(x, y, z) = (x + 2y - z, \ 2x + 4y + z)$. Both coordinates are linear in $(x, y, z)$, so $f$ is linear. The kernel is the set of solutions of $x + 2y - z = 0$ and $2x + 4y + z = 0$. Add the two equations: $3x + 6y = 0$, so $x = -2y$. Then $z = x + 2y = 0$. So $\ker f = \{(-2t, t, 0) : t \in \mathbb{R}\} = \mathbb{R}(-2, 1, 0)$, a line. The range contains $f(e_1) = (1, 2)$ and $f(e_3) = (-1, 1)$. These two vectors span $\mathbb{R}^2$: a vector $(a, b)$ equals $s(1, 2) + t(-1, 1)$ for $s = (a + b)/3$ and $t = (b - 2a)/3$. So $f$ is surjective and not injective. The dimensions satisfy $1 + 2 = 3$, an instance of rank-nullity in Chapter 2.

**Example (The derivative).** Let $P_n$ be the real vector space of the polynomials of degree at most $n$. The derivative $D : P_n \to P_n$, $D p = p'$, is linear by the sum rule and the constant factor rule. Its kernel is the space of the constants, $P_0$. Its range is $P_{n-1}$: $D$ lowers the degree by one, and each polynomial $\sum_{k < n} a_k x^k$ is the derivative of $\sum_{k < n} \frac{a_k}{k+1} x^{k+1}$. So $D$ is neither injective nor surjective on $P_n$. The power $D^{n+1}$ is the zero map, so $D$ is a nilpotent element of the ring $\operatorname{End}(P_n)$.

**Example (Endomorphisms that do not commute).** On $\mathbb{R}^2$, let $f(x, y) = (y, x)$, the swap, and $g(x, y) = (x, 0)$, the projection on the first axis. Then $(f g)(x, y) = f(x, 0) = (0, x)$, and $(g f)(x, y) = g(y, x) = (y, 0)$. So $f g \neq g f$, and $\operatorname{End}(\mathbb{R}^2)$ is not a commutative ring. It also has zero divisors: $g \circ h = 0$ for the projection $h(x, y) = (0, y)$ on the second axis, while $g \neq 0$ and $h \neq 0$.

**Counterexample (A bijection that is not linear).** The map $\mathbb{C} \to \mathbb{C}$, $z \mapsto \bar{z}$, is additive and bijective. It is $\mathbb{R}$-linear. It is not $\mathbb{C}$-linear: $\overline{i \cdot 1} = -i$, while $i \cdot \bar{1} = i$. It is semilinear for the conjugation of $\mathbb{C}$, the case that `M →ₛₗ[σ] N` covers. The ring matters in the definition of linearity.

### The library around it

The definition of `LinearMap` is in `Mathlib.Algebra.Module.LinearMap.Defs`, with `LinearMap.id`, `LinearMap.comp` and the classes `LinearMapClass` and `SemilinearMapClass`. These classes let one lemma, such as `map_add`, serve every kind of bundled map: linear maps, linear equivalences, algebra maps and continuous linear maps. The kernel and the range are in `Mathlib.Algebra.Module.Submodule.Ker` and `Mathlib.Algebra.Module.Submodule.Range`. The equivalences are in `Mathlib.Algebra.Module.Equiv.Defs`, and the ring `Module.End` is in `Mathlib.Algebra.Module.LinearMap.End`.

The linear maps `M →ₗ[R] N` form a module over `R` when `R` is commutative. The proof needs commutativity: $(r f)(s x) = r f(s x) = r s f(x)$ must equal $s (r f)(x) = s r f(x)$.

### Exercises

1. (A) Find the kernel and the range of $f : \mathbb{Q}^3 \to \mathbb{Q}^3$, $f(x, y, z) = (x - y, y - z, z - x)$. Hint: the three coordinates of $f(v)$ add up to $0$.
2. (A) Show that the map $P_n \to \mathbb{R}$, $p \mapsto p(2)$, is linear, and find its kernel. Hint: $p(2) = 0$ if and only if $x - 2$ divides $p$.
3. (A) Show that a linear map $f : M \to N$ with $\ker f = 0$ sends a submodule $M_0$ onto a submodule isomorphic to $M_0$.
4. (B) Let $f : M \to M$ be linear with $f \circ f = f$. Show that $M = \ker f + \operatorname{im} f$ and $\ker f \cap \operatorname{im} f = 0$. Hint: $x = (x - f(x)) + f(x)$.
5. (B) Show that $\operatorname{Hom}_{\mathbb{Z}}(\mathbb{Z}/m, \mathbb{Z}/n)$ has $\gcd(m, n)$ elements. Hint: a linear map is fixed by the image $a$ of $1$, and $m a = 0$ in $\mathbb{Z}/n$.
6. (B) Let $f, g \in \operatorname{End}(M)$ with $f g = g f$. Show that $g(\ker f) \subseteq \ker f$ and $g(\operatorname{im} f) \subseteq \operatorname{im} f$.
7. (B) Show that $\operatorname{Hom}_{\mathbb{Z}}(\mathbb{Q}, \mathbb{Z}) = 0$. Hint: if $f(1/n) = a_n$, then $n a_n = f(1)$ for each $n$.
8. (C) On the $\mathbb{N}$-module $\mathbb{N}$, find an $\mathbb{N}$-linear map $f : \mathbb{N} \times \mathbb{N} \to \mathbb{N}$ with $f(x) = 0$ only for $x = 0$, which is not injective. Explain which step of the proof of the theorem on injectivity fails. Hint: try $f(a, b) = a + b$.

### Notes and history

Linear maps entered mathematics as linear substitutions of variables, in the work of Gauss on quadratic forms and of Cayley on invariants. The abstract notion, a map between vector spaces that respects the operations, is due to Peano and was made standard by Banach in the 1920s and by the algebra books of van der Waerden in 1930.

In Mathlib, the files on linear maps and submodules grew from the early work of Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl and Mario Carneiro, and the kernel and range files from Kevin Buzzard and Yury Kudryashov. The general semilinear form was added later, so that conjugate linear maps of complex inner product spaces fit in the same frame as linear maps.

### Reference

<?reference?>
