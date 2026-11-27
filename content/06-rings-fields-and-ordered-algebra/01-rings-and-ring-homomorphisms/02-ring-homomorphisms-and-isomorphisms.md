---
title: Ring homomorphisms and isomorphisms
kind: theory
modules:
  - Mathlib.Algebra.Ring.Hom.Defs
  - Mathlib.Algebra.Ring.Equiv
explains:
  E3: [RingHom, RingEquiv]
  E2: [RingHomClass, RingHom.comp, RingHom.id, RingHom.ext, RingEquiv.symm, RingEquiv.trans, RingEquiv.ofBijective, RingEquiv.toRingHom]
  E1: auto
families: []
requires: [V05.C02]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Ring homomorphisms and isomorphisms

### Overview

A ring homomorphism is a map between rings that keeps the sum, the product and the unit. Homomorphisms compare rings: an injective one shows a ring inside another, a surjective one shows a ring as a simplified image of another, and a bijective one shows that two rings are the same up to the names of the elements. The main examples are the reduction $\mathbb{Z} \to \mathbb{Z}/n$, the evaluation of a function at a point, complex conjugation, and the inclusions $\mathbb{Z} \subseteq \mathbb{Q} \subseteq \mathbb{R} \subseteq \mathbb{C}$.

The main theorem of the section says that for each ring $R$ there is exactly one ring homomorphism $\mathbb{Z} \to R$. So $\mathbb{Z}$ is the initial ring, and every ring contains a homomorphic image of $\mathbb{Z}$. This image is the source of the characteristic of Chapter 4. The section also decides when there is a homomorphism $\mathbb{Z}/n \to R$, and it proves the first case of the Chinese remainder theorem, $\mathbb{Z}/6 \cong \mathbb{Z}/2 \times \mathbb{Z}/3$, by a direct computation. Chapter 2 proves the general theorem.

### Definitions

**Definition (Ring homomorphism).** Let $R$ and $S$ be rings. A ring homomorphism is a map $f : R \to S$ with
$$f(a + b) = f(a) + f(b), \qquad f(a b) = f(a) f(b), \qquad f(1) = 1$$
for all $a, b \in R$. The same definition applies to semirings, with the extra condition $f(0) = 0$.

The condition $f(1) = 1$ does not follow from the other two. The map $\mathbb{Z} \to \mathbb{Z} \times \mathbb{Z}$, $n \mapsto (n, 0)$, keeps sums and products, but it sends $1$ to $(1, 0)$, which is not the unit $(1, 1)$. With the definition above it is not a ring homomorphism. The condition $f(0) = 0$ follows from additivity in a ring, by the theorem on group homomorphisms of Volume 5, but not in a semiring.

::: mathlib
`RingHom` · `Mathlib.Algebra.Ring.Hom.Defs`

The type `R →+* S` of the ring homomorphisms. It is a structure that extends `R →* S` (the monoid homomorphisms for the product) and `R →+ S` (for the sum), so it has four fields: `map_one'`, `map_mul'`, `map_zero'`, `map_add'`. It is stated for `NonAssocSemiring`, so it covers semirings and rings. A homomorphism `f` is applied to `a` as `f a` by the coercion `FunLike`. The lemmas for its values are the generic `map_add`, `map_mul`, `map_one`, `map_zero`, `map_neg`, `map_sub`, `map_pow` and `map_natCast`, which apply to each type of homomorphisms.

<?decl RingHom?>
:::

::: mathlib
`RingHomClass` · `Mathlib.Algebra.Ring.Hom.Defs`

The class of the types `F` of maps that behave as ring homomorphisms. `RingHom` is one instance, `RingEquiv` is another, and the algebra homomorphisms of Chapter 8 are a third. A lemma stated with `[RingHomClass F R S] (f : F)` applies to all of them. This is why `map_mul f a b` works for an isomorphism as well as for a homomorphism, with no conversion.

<?decl RingHomClass?>
:::

**Definition (Isomorphism).** A ring isomorphism is a bijective ring homomorphism. Two rings $R$ and $S$ are isomorphic, $R \cong S$, if there is an isomorphism $R \to S$. An automorphism of $R$ is an isomorphism $R \to R$.

::: mathlib
`RingEquiv` · `Mathlib.Algebra.Ring.Equiv`

The type `R ≃+* S`. It is a structure that extends the equivalence `R ≃ S` of types, so it stores the map and its inverse, with the two fields `map_mul'` and `map_add'`. The inverse is data, so `e.symm` computes and `e.symm (e a) = a` holds by a lemma. The automorphisms of `R` form the group `RingAut R`.

<?decl RingEquiv?>
:::

::: mathlib
`RingEquiv.ofBijective` · `Mathlib.Algebra.Ring.Equiv`

The theorem that a bijective homomorphism is an isomorphism, as a construction: `RingEquiv.ofBijective f hf : R ≃+* S`. The inverse map is chosen from the proof of bijectivity, so it is `noncomputable` in general.

<?decl RingEquiv.ofBijective?>
:::

### Theorems and proofs

**Theorem (Elementary properties).** Let $f : R \to S$ be a ring homomorphism. Then $f(0) = 0$, $f(-a) = -f(a)$, $f(a - b) = f(a) - f(b)$, $f(a^n) = f(a)^n$ and $f(n \cdot a) = n \cdot f(a)$ for $n \in \mathbb{Z}$. If $a$ has a multiplicative inverse $a^{-1}$, then $f(a)$ has the inverse $f(a^{-1})$.

*Proof.* The map $f$ is a homomorphism of the additive groups. So it sends $0$ to $0$ and $-a$ to $-f(a)$, by Volume 5, and then $f(a - b) = f(a) + f(-b) = f(a) - f(b)$. The rule for multiples is the rule for powers in an additive group. The rule $f(a^n) = f(a)^n$ follows by induction on $n$ from $f(1) = 1$ and $f(a^{n+1}) = f(a^n) f(a)$. Last, $f(a) f(a^{-1}) = f(a a^{-1}) = f(1) = 1$, and in the same way $f(a^{-1}) f(a) = 1$. $\square$

**Theorem (Composition and inverse).** The composite of two ring homomorphisms is a ring homomorphism, and the identity is one. If $f : R \to S$ is a ring isomorphism, then the inverse map $f^{-1} : S \to R$ is a ring homomorphism.

*Proof.* Let $f : R \to S$ and $g : S \to T$. Then $g(f(a + b)) = g(f(a) + f(b)) = g(f(a)) + g(f(b))$, and the same for the product, and $g(f(1)) = g(1) = 1$. For the inverse, let $x, y \in S$, and put $a = f^{-1}(x)$, $b = f^{-1}(y)$. Then $f(a b) = f(a) f(b) = x y$, so $f^{-1}(x y) = a b = f^{-1}(x) f^{-1}(y)$. The same argument works for the sum, and $f^{-1}(1) = 1$ because $f(1) = 1$. $\square$

So isomorphism is an equivalence relation on rings, and the automorphisms of a ring form a group under composition.

::: mathlib
`RingHom.comp` · `Mathlib.Algebra.Ring.Hom.Defs`

The composite `g.comp f : R →+* T`, with `(g.comp f) a = g (f a)` by `RingHom.comp_apply`. The identity is `RingHom.id R`. For isomorphisms the composite is `e.trans e'`, in the order of the arrows, and the inverse is `e.symm`.

<?decl RingHom.comp?>
:::

::: mathlib
`RingEquiv.trans` · `Mathlib.Algebra.Ring.Equiv`

The composite of two isomorphisms `R ≃+* S` and `S ≃+* T`. Note the order: `e.trans e'` applies `e` first, unlike `g.comp f`.

<?decl RingEquiv.trans?>
:::

::: mathlib
`RingEquiv.symm` · `Mathlib.Algebra.Ring.Equiv`

The inverse isomorphism. The proof that it keeps the operations is the computation of the text.

<?decl RingEquiv.symm?>
:::

**Theorem (The integers are initial).** Let $R$ be a ring. There is exactly one ring homomorphism $\chi : \mathbb{Z} \to R$. It is $\chi(n) = n \cdot 1_R$, the $n$-th multiple of the unit.

*Proof.* Uniqueness. Let $f : \mathbb{Z} \to R$ be a ring homomorphism. Then $f(1) = 1_R$. For $n \ge 0$, induction on $n$ gives $f(n) = n \cdot 1_R$: the case $n = 0$ is $f(0) = 0$, and $f(n + 1) = f(n) + f(1) = n \cdot 1_R + 1_R = (n + 1) \cdot 1_R$. For $n < 0$, $f(n) = -f(-n) = -((-n) \cdot 1_R) = n \cdot 1_R$. So $f = \chi$.

Existence. The map $\chi(n) = n \cdot 1_R$ is a homomorphism of additive groups, $(n + m) \cdot 1_R = n \cdot 1_R + m \cdot 1_R$, by the rules for multiples in a group. It sends $1$ to $1_R$. For the product, first let $n \ge 0$. Then, by the distributive law applied $n$ times,
$$(n \cdot 1_R)(m \cdot 1_R) = \underbrace{(m \cdot 1_R) + \dots + (m \cdot 1_R)}_{n} = (n m) \cdot 1_R.$$
For $n < 0$, the rule of signs of Section 1 gives $(n \cdot 1_R)(m \cdot 1_R) = -(((-n) \cdot 1_R)(m \cdot 1_R)) = -((-n) m \cdot 1_R) = (n m) \cdot 1_R$. $\square$

::: mathlib
`RingHom.ext_int` · `Mathlib.Data.Int.Cast.Lemmas`

The uniqueness: any two `f g : ℤ →+* R` are equal. The homomorphism itself is `Int.castRingHom R`, the cast `(n : R)`, from Volume 2. In a proof, the lemma `map_intCast f n : f n = n` says that every ring homomorphism commutes with the casts.

<?decl RingHom.ext_int?>
:::

**Theorem (Homomorphisms out of $\mathbb{Z}/n$).** Let $n \ge 1$ and let $R$ be a ring. There is a ring homomorphism $\mathbb{Z}/n \to R$ if and only if $n \cdot 1_R = 0$. In that case it is unique, and it sends the class $[k]$ to $k \cdot 1_R$.

*Proof.* Let $\pi : \mathbb{Z} \to \mathbb{Z}/n$ be the reduction, a surjective ring homomorphism. Suppose that $g : \mathbb{Z}/n \to R$ is a ring homomorphism. Then $g \circ \pi$ is a ring homomorphism $\mathbb{Z} \to R$, so $g \circ \pi = \chi$ by the previous theorem, and $g([k]) = k \cdot 1_R$. In particular $n \cdot 1_R = g([n]) = g(0) = 0$. This proves the condition and the uniqueness.

Conversely, suppose $n \cdot 1_R = 0$. Define $g([k]) = k \cdot 1_R$. It is well defined: if $[k] = [k']$, then $k - k' = n q$ for some $q \in \mathbb{Z}$, and $k \cdot 1_R - k' \cdot 1_R = q \cdot (n \cdot 1_R) = 0$. It keeps the sum, the product and the unit because $\chi$ does: $g([k][l]) = g([k l]) = \chi(k l) = \chi(k) \chi(l) = g([k]) g([l])$, and the same for the sum. $\square$

In particular there is no ring homomorphism $\mathbb{Z}/n \to \mathbb{Z}$ for $n \ge 1$, because $n \cdot 1 = n \ne 0$ in $\mathbb{Z}$. There is a homomorphism $\mathbb{Z}/m \to \mathbb{Z}/n$ if and only if $n$ divides $m$, because $m \cdot 1 = 0$ in $\mathbb{Z}/n$ means $n \mid m$.

::: mathlib
`ZMod.castHom` · `Mathlib.Data.ZMod.Basic`

The homomorphism `ZMod.castHom (h : m ∣ n) R : ZMod n →+* R` for a ring `R` with `[CharP R m]`. The class `CharP R m` of Chapter 4 says that `(k : R) = 0` exactly when `m ∣ k`. So Mathlib states the theorem in terms of the characteristic, with a divisibility, rather than with the condition $n \cdot 1_R = 0$ of the text.

<?decl ZMod.castHom?>
:::

**Theorem (Homomorphisms that agree on generators).** Let $f, g : \mathbb{Q} \to S$ be ring homomorphisms. Then $f = g$.

*Proof.* The restrictions of $f$ and $g$ to $\mathbb{Z}$ are ring homomorphisms $\mathbb{Z} \to S$, so they agree by the theorem on $\mathbb{Z}$. Let $a / b \in \mathbb{Q}$ with $b \ne 0$. The element $b$ has the inverse $1/b$ in $\mathbb{Q}$, so $f(b)$ is invertible in $S$ with inverse $f(1/b)$, by the elementary properties. The same holds for $g$. Since $f(b) = g(b)$, the inverses agree: $f(1/b) = g(1/b)$, because an inverse in a monoid is unique. So $f(a/b) = f(a) f(1/b) = g(a) g(1/b) = g(a/b)$. $\square$

::: mathlib
`RingHom.ext_rat` · `Mathlib.Data.Rat.Cast.Defs`

The uniqueness of ring homomorphisms out of `ℚ`, in the form `f = g` for `f g : ℚ →+* R`, for any semiring `R`. The existence holds when `R` is a division ring of characteristic zero, by the cast `Rat.castHom`.

<?decl RingHom.ext_rat?>
:::

### Examples

**Example (The Chinese remainder theorem for $6$).** By the theorem on $\mathbb{Z}/n$, there are ring homomorphisms $\mathbb{Z}/6 \to \mathbb{Z}/2$ and $\mathbb{Z}/6 \to \mathbb{Z}/3$, since $2$ and $3$ divide $6$. Together they give a ring homomorphism $\varphi : \mathbb{Z}/6 \to \mathbb{Z}/2 \times \mathbb{Z}/3$, $\varphi([k]) = ([k]_2, [k]_3)$. Its values are:

| $k$ | $0$ | $1$ | $2$ | $3$ | $4$ | $5$ |
|---|---|---|---|---|---|---|
| $\varphi([k])$ | $(0, 0)$ | $(1, 1)$ | $(0, 2)$ | $(1, 0)$ | $(0, 1)$ | $(1, 2)$ |

The six values are distinct, and the target has six elements. So $\varphi$ is a bijection, and $\mathbb{Z}/6 \cong \mathbb{Z}/2 \times \mathbb{Z}/3$ as rings. The table also identifies the idempotents of $\mathbb{Z}/6$: they correspond to $(0,0), (1,1), (1,0), (0,1)$, that is, to $0, 1, 3, 4$, as found in Section 1.

**Counterexample (The coprimality is needed).** There is no ring isomorphism $\mathbb{Z}/4 \to \mathbb{Z}/2 \times \mathbb{Z}/2$. In the product, $2 \cdot x = 0$ for each $x$. In $\mathbb{Z}/4$, $2 \cdot 1 = 2 \ne 0$. An isomorphism $f$ would give $2 \cdot f(1) = f(2) \ne 0$, but $f(1) = (1, 1)$ and $2 \cdot (1, 1) = 0$. The two rings even have different additive groups: $\mathbb{Z}/4$ is cyclic and $\mathbb{Z}/2 \times \mathbb{Z}/2$ is not.

**Example (Evaluation).** Let $X$ be a set, $R$ a ring and $x_0 \in X$. The map $\mathrm{ev}_{x_0} : R^X \to R$, $f \mapsto f(x_0)$, is a ring homomorphism, because the operations of $R^X$ are defined at each point. It is surjective: the constant function with value $r$ maps to $r$. In the same way the projections $R \times S \to R$ and $R \times S \to S$ are surjective ring homomorphisms.

**Example (Complex conjugation).** The map $z \mapsto \bar z$ on $\mathbb{C}$, $\overline{a + b i} = a - b i$, is a ring automorphism. For the product, let $z = a + b i$ and $w = c + d i$. Then $z w = (a c - b d) + (a d + b c) i$, so $\overline{z w} = (a c - b d) - (a d + b c) i$. On the other side, $\bar z \bar w = (a - b i)(c - d i) = (a c - b d) - (a d + b c) i$. The sum and the unit are clear. The map is its own inverse, so it is bijective. It fixes each real number. Exercise 8 shows that the only automorphisms of $\mathbb{C}$ that fix $\mathbb{R}$ are the identity and conjugation.

**Counterexample (A map that keeps only the sum).** The map $\mathbb{Z} \to \mathbb{Z}$, $n \mapsto 2 n$, keeps the sum but not the product: $2 \cdot (1 \cdot 1) = 2$ while $(2 \cdot 1)(2 \cdot 1) = 4$. It is a group homomorphism, not a ring homomorphism, in agreement with the theorem that the identity is the only ring homomorphism $\mathbb{Z} \to \mathbb{Z}$.

**Example (A ring with no homomorphism to a field of characteristic zero).** The ring $\mathbb{Z}/n$, for $n \ge 1$, has no homomorphism to $\mathbb{Q}$, $\mathbb{R}$ or $\mathbb{C}$, since $n \cdot 1 \ne 0$ there. The ring $\mathbb{Q}$ has no homomorphism to $\mathbb{Z}/p$: the element $p$ is invertible in $\mathbb{Q}$, and its image $p \cdot 1 = 0$ is not invertible. So the ring homomorphisms give an obstruction that the additive groups alone do not see.

### The library around it

The bundled homomorphisms of Mathlib follow one pattern for each structure: `M →* N` for monoids, `R →+* S` for rings, `A →ₐ[R] B` for algebras (Chapter 8), and `≃*`, `≃+*`, `≃ₐ[R]` for the isomorphisms. Each type has an `ext` lemma (`RingHom.ext : (∀ x, f x = g x) → f = g`), a `comp` and an `id`, and the lemmas `coe_comp`, `comp_apply` and `id_apply`. The value lemmas are not stated for each type: the generic `map_add`, `map_mul` and their relatives, stated with `RingHomClass`, apply to all. The simp normal form writes `f (a * b)` as `f a * f b`.

To build a homomorphism, give a structure: `{ toFun := ..., map_one' := ..., map_mul' := ..., map_zero' := ..., map_add' := ... }`. When the target is a ring, `RingHom.mk'` builds a ring homomorphism from a monoid homomorphism `f : R →* S` and a proof that `f` is additive, since `map_zero'` follows. The products have `RingHom.fst`, `RingHom.snd` and `RingHom.prod f g : R →+* S × T`. The evaluation at a point of a function ring is `Pi.evalRingHom`.

Common errors of a learner:

- A `RingHom` is not a function. The coercion turns it into one, and `⇑f` in a goal is that coercion. A lemma about functions, such as `Function.Injective f`, is about `⇑f`.
- `g.comp f` and `e.trans e'` take the arguments in opposite orders.
- `RingEquiv.ofBijective` is noncomputable, so `#eval` of its inverse fails. Build the inverse by hand when it must compute.
- The theorem `map_neg` needs a ring, not a semiring. In `ℕ` there is no negation.

### Exercises

1. (A) Show that $\mathbb{Z} \to \mathbb{Z}/n$, $k \mapsto [k]$, is a surjective ring homomorphism.
2. (A) Find all the ring homomorphisms $\mathbb{Z}/12 \to \mathbb{Z}/4$, $\mathbb{Z}/4 \to \mathbb{Z}/12$ and $\mathbb{Z}/6 \to \mathbb{Z}/6$.
3. (A) Show that $\mathbb{Z} \times \mathbb{Z}$ has exactly two ring homomorphisms to $\mathbb{Z}$. Hint: the image of $(1, 0)$ is an idempotent of $\mathbb{Z}$.
4. (A) Show that the map $\mathbb{Z}/10 \to \mathbb{Z}/2 \times \mathbb{Z}/5$, $[k] \mapsto ([k], [k])$, is an isomorphism. Find the element that maps to $(1, 0)$.
5. (B) Show that a ring homomorphism $f : R \to S$ with $S \neq 0$ satisfies $f(a) \ne 0$ for each unit $a$ of $R$. Deduce that every ring homomorphism from a field to a nonzero ring is injective. Hint: if $f(a) = f(b)$, then $a - b$ maps to $0$.
6. (B) Let $f : R \to S$ be a ring homomorphism. Show that $f(e)$ is an idempotent for each idempotent $e$, and that $f(a)$ is nilpotent for each nilpotent $a$.
7. (B) Show that $\mathbb{Z}[i] = \{a + b i : a, b \in \mathbb{Z}\}$ has exactly two ring automorphisms. Hint: an automorphism sends $i$ to a square root of $-1$.
8. (B) Let $\sigma$ be a ring automorphism of $\mathbb{C}$ with $\sigma(r) = r$ for each $r \in \mathbb{R}$. Show that $\sigma$ is the identity or complex conjugation.
9. (C) Show that the only ring homomorphism $\mathbb{R} \to \mathbb{R}$ is the identity. Hint: a homomorphism sends squares to squares, so it is monotone; it fixes $\mathbb{Q}$, and a monotone map that fixes $\mathbb{Q}$ fixes $\mathbb{R}$. Mathlib has this as the instance `Real.RingHom.unique`.
10. (C) Show that $\mathbb{Q}[\sqrt 2] = \{a + b\sqrt 2 : a, b \in \mathbb{Q}\}$ and $\mathbb{Q}[\sqrt 3]$ are not isomorphic rings. Hint: an isomorphism would send $\sqrt 2$ to a square root of $2$ in $\mathbb{Q}[\sqrt 3]$; solve $(a + b \sqrt 3)^2 = 2$.

### Notes and history

The idea of a homomorphism of rings grew out of the work of Dedekind and Kronecker on number fields, where the embeddings of a number field into $\mathbb{C}$ are the main objects. Noether and her school made homomorphisms and isomorphisms the central tool of algebra in the 1920s, and van der Waerden's *Moderne Algebra* (1930) fixed the modern vocabulary. That every ring has exactly one homomorphism from $\mathbb{Z}$ is the statement that $\mathbb{Z}$ is an initial object in the category of rings (Volume 24). The standard references are Dummit-Foote, Section 7.3, and Jacobson, *Basic Algebra I*, Section 2.7.

In Mathlib the bundled homomorphisms replaced unbundled predicates such as `is_ring_hom` in 2019 and 2020. The classes `RingHomClass` and `FunLike` came with the port to Lean 4, so that one lemma `map_mul` serves every kind of homomorphism.

### Reference

<?reference?>
