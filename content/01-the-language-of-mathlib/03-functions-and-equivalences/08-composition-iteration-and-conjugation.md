---
title: Composition, iteration and conjugation
kind: api
modules:
  - Mathlib.Logic.Function.Defs
  - Mathlib.Logic.Function.Const
  - Mathlib.Logic.Function.Iterate
  - Mathlib.Logic.Function.Conjugate
  - Mathlib.Logic.Function.Coequalizer
  - Mathlib.Logic.Function.CompTypeclasses
  - Mathlib.Logic.Function.DependsOn
  - Mathlib.Logic.Function.FiberPartition
  - Mathlib.Logic.Function.FromTypes
  - Mathlib.Logic.Function.OfArity
  - Mathlib.Data.SubtypeNeLift
  - Mathlib.Logic.OpClass
explains:
  E2: [Function.iterate_add, Function.iterate_succ', Function.Semiconj.comp_right, Function.Semiconj.iterate_right, Function.Commute.comp_iterate, Function.isConst_iff_exists_eq_const, Function.Coequalizer.desc_mk]
  E1: auto
families: []
requires: [V01.C02]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Composition, iteration and conjugation

### Overview

The first section of this chapter studies one function at a time: is it injective, surjective or bijective? This section studies the operations that make new functions from old ones. The modules hold the basic combinators of composition and pairing, the iterates $f^{[n]}$ of a self map, the constant functions, and the relation of semiconjugacy $f \circ g_a = g_b \circ f$. They also hold a few small constructions: the coequalizer of two maps, the type of fibers of a map, the functions that depend only on some coordinates, and the function types of a fixed arity.

A reader needs these modules in every later volume. Dynamics uses iterates and fixed points. Algebra uses semiconjugacy: a monoid homomorphism is a map that semiconjugates multiplication. The order of composition and the order of iteration are the most common sources of small errors, so the section states the defining equations with care.

### The library around it

#### Combinators

The module `Mathlib.Logic.Function.Defs` collects the combinators on plain functions. Composition is the core operation $g \circ f$, and `Function.comp_assoc` states $(f \circ g) \circ h = f \circ (g \circ h)$; it holds by `rfl`. The dependent composition `Function.dcomp` has the notation `f ∘' g` and composes a dependent function after an ordinary one. For a function $f : \beta \to \beta \to \varphi$ and a map $g : \alpha \to \beta$, the function `Function.onFun f g` sends $x, y$ to $f(g(x), g(y))$; in the scope `Function` it has the notation `f on g`. It turns a relation on $\beta$ into a relation on $\alpha$. The function `Function.swap` exchanges the two arguments of a dependent binary function, and `Function.flip_def` unfolds the core `flip`.

The pairing `Function.prod f g` sends $i$ to $(f(i), g(i))$, and the diagonal `Function.diag` sends $a$ to $(a, a)$. The lemmas follow one pattern: a projection after a pairing is a component, and a pairing after a map is a pairing of composites.

| Lean name | Statement |
|---|---|
| `Function.fst_comp_prod` | `Prod.fst ∘ Function.prod f g = f` |
| `Function.prod_comp` | `Function.prod f g ∘ h = Function.prod (f ∘ h) (g ∘ h)` |
| `Function.map_comp_prod` | `Prod.map h k ∘ Function.prod f g = Function.prod (h ∘ f) (k ∘ g)` |
| `Function.prod_fst_snd` | `Function.prod Prod.fst Prod.snd = id` |
| `Function.prod_id_id` | `Function.prod id id = Function.diag` |
| `Function.diag_comp` | `Function.diag ∘ f = Function.prod f f` |
| `Function.diag_injective` | the diagonal is injective |

The binary forms `Function.bicompl` and `Function.bicompr` compose a binary function with maps on the inputs or on the output. The lemmas `Function.uncurry_bicompl` and `Function.uncurry_bicompr` translate them into ordinary composition after uncurrying. The predicate `Function.IsFixedPt f x` means $f(x) = x$, and `Function.forall_isFixedPt_iff` states that every point is fixed exactly when $f = \mathrm{id}$. The map `Pi.map` applies a family of maps coordinatewise. The same module also defines `Function.Bijective`, which the first section of this chapter studies.

#### Iterates

For $f : \alpha \to \alpha$ and $n : \mathbb{N}$, the iterate `Nat.iterate f n` has the notation `f^[n]`. The definition is by recursion on $n$ with $f^{[0]}(a) = a$ and $f^{[n + 1]}(a) = f^{[n]}(f(a))$. So the new application of $f$ goes on the inside. The two forms of the successor rule are then of different kinds:

- `Function.iterate_succ` states $f^{[n + 1]} = f^{[n]} \circ f$. It holds by definition.
- `Function.iterate_succ'` states $f^{[n + 1]} = f \circ f^{[n]}$. It needs a proof.

**Theorem (Iterates add).** For $f : \alpha \to \alpha$ and $m, n : \mathbb{N}$, $f^{[m + n]} = f^{[m]} \circ f^{[n]}$.

*Proof.* Induction on $n$. For $n = 0$ both sides are $f^{[m]}$, since $f^{[0]} = \mathrm{id}$. For the step, $f^{[m + (n + 1)]} = f^{[(m + n) + 1]} = f^{[m + n]} \circ f$ by the definition. By the induction hypothesis this is $f^{[m]} \circ f^{[n]} \circ f$, and $f^{[n]} \circ f = f^{[n + 1]}$ by the definition again. $\square$

The case $m = 1$ gives $f^{[1 + n]} = f \circ f^{[n]}$, and $1 + n = n + 1$. This is the form `iterate_succ'`.

The lemma is `Function.iterate_add`, and `Function.iterate_add_apply` is the form at a point. The other laws are `Function.iterate_zero`, `Function.iterate_one`, `Function.iterate_id`, `Function.iterate_mul` ($f^{[mn]} = (f^{[m]})^{[n]}$) and `Function.iterate_comm`. The names with `_apply` state the same laws at a point and are the simp forms. Iteration preserves the classes of the first section: `Function.Injective.iterate`, `Function.Surjective.iterate`, `Function.Bijective.iterate`, `Function.LeftInverse.iterate` and `Function.RightInverse.iterate`. A fixed point of $f$ is fixed by all iterates, by `Function.iterate_fixed`. For an injective $f$, `Function.iterate_cancel` states that $f^{[m]}(a) = f^{[n]}(a)$ gives $f^{[m - n]}(a) = a$. An involution is a map with $f^{[2]} = \mathrm{id}$, by `Function.involutive_iff_iter_2_eq_id`. A fold with a constant step is an iterate: `List.foldl_const` and `List.foldr_const`. The recursor `Function.Iterate.rec` proves a property of $f^{[n]}(a)$ from the property of $a$ and its stability under $f$.

#### Semiconjugacy and commuting maps

**Definition (Semiconjugacy).** A map $f : \alpha \to \beta$ *semiconjugates* $g_a : \alpha \to \alpha$ to $g_b : \beta \to \beta$ if $f \circ g_a = g_b \circ f$, that is, $f(g_a(x)) = g_b(f(x))$ for every $x$. Two maps $f, g : \alpha \to \alpha$ *commute* if $f \circ g = g \circ f$.

The module `Mathlib.Logic.Function.Conjugate` defines `Function.Semiconj f ga gb` and `Function.Commute f g`. The second is by definition `Function.Semiconj f g g`; the lemmas `Function.Commute.semiconj` and `Function.Semiconj.commute` pass between the two. The point form is `Function.Semiconj.eq`, and `Function.semiconj_iff_comp_eq` gives the form with composition. A semiconjugacy is a morphism of dynamical systems: a monoid homomorphism $\varphi$ semiconjugates left multiplication by $a$ to left multiplication by $\varphi(a)$.

**Theorem (Composites of semiconjugated maps).** If $f$ semiconjugates $g_a$ to $g_b$ and $g_a'$ to $g_b'$, then $f$ semiconjugates $g_a \circ g_a'$ to $g_b \circ g_b'$.

*Proof.* For $x : \alpha$, $f(g_a(g_a'(x))) = g_b(f(g_a'(x))) = g_b(g_b'(f(x)))$, by the two hypotheses in turn. $\square$

This is `Function.Semiconj.comp_right`. With `Function.Semiconj.id_right`, which states that $f$ semiconjugates $\mathrm{id}$ to $\mathrm{id}$, an induction on $n$ gives `Function.Semiconj.iterate_right`: $f$ semiconjugates $g_a^{[n]}$ to $g_b^{[n]}$. In the other direction, `Function.Semiconj.trans` and `Function.Semiconj.comp_left` compose two semiconjugating maps.

**Theorem (Iterates of a composite).** If $f$ and $g$ commute, then $(f \circ g)^{[n]} = f^{[n]} \circ g^{[n]}$.

*Proof.* Induction on $n$. The case $n = 0$ is $\mathrm{id} = \mathrm{id} \circ \mathrm{id}$. For the step, $(f \circ g)^{[n + 1]} = (f \circ g) \circ (f \circ g)^{[n]} = f \circ g \circ f^{[n]} \circ g^{[n]}$. The map $g$ commutes with $f^{[n]}$, by the iterate form of the previous theorem. So the composite is $f \circ f^{[n]} \circ g \circ g^{[n]} = f^{[n + 1]} \circ g^{[n + 1]}$. $\square$

This is `Function.Commute.comp_iterate`. The lemmas `Function.Commute.iterate_left`, `Function.Commute.iterate_right` and `Function.Commute.iterate_iterate` give the commuting of iterates. Every map commutes with its own iterates, by `Function.Commute.self_iterate`. The inverse forms `Function.Semiconj.inverse_left` and `Function.Semiconj.inverses_right` move a semiconjugacy across inverse maps.

The binary form `Function.Semiconj₂ f ga gb` means $f(g_a(x, y)) = g_b(f(x), f(y))$: the map $f$ is a homomorphism from $(\alpha, g_a)$ to $(\beta, g_b)$. The lemmas `Function.Semiconj₂.isAssociative_right` and `Function.Semiconj₂.isIdempotent_right` transport associativity and idempotence along a surjective $f$. The forms `_left` transport them back along an injective $f$.

#### Constant functions

A function $f : \alpha \to \beta$ is *constant* if $f(x) = f(y)$ for all $x$ and $y$. This is `Function.IsConst f`, and `Function.IsConstOn f s` is the same condition for $x, y \in s$. The definition does not name the constant value, so it holds on an empty type with no value to name.

**Theorem (Constant functions have a value).** Let $\beta$ be nonempty. Then $f$ is constant if and only if $f = \mathrm{const}\ b$ for some $b : \beta$.

*Proof.* If $f = \mathrm{const}\ b$, then $f(x) = b = f(y)$. For the converse, if $\alpha$ has a point $a$, take $b = f(a)$; then $f(x) = f(a) = b$ for every $x$. If $\alpha$ is empty, take any $b$ in the nonempty $\beta$; the two functions agree on all points, since there are none. $\square$

This is `Function.isConst_iff_exists_eq_const`. With a nonempty domain the lemma `Function.isConst_iff_exists_eq_const_of_nonempty_domain` needs no hypothesis on $\beta$. The other results compare constancy with the classes of the first section: `Function.Injective.isConst_iff` states that an injective map is constant exactly when its domain is a subsingleton, and `Function.isConst_and_surjective_iff` describes the surjective constant maps. The links with sets are `Set.subsingleton_range_iff` and `Set.subsingleton_image_iff`. The forms on a set follow the same names with `IsConstOn` and `isConstOn`.

#### Small constructions

The module `Mathlib.Logic.Function.Coequalizer` defines, for two maps $f, g : \alpha \to \beta$, the type `Function.Coequalizer f g`. It is the quotient of $\beta$ by the relation generated by $f(x) \sim g(x)$. The map `Function.Coequalizer.mk f g` is the projection, and `Function.Coequalizer.condition` states that it identifies $f(x)$ with $g(x)$.

**Theorem (Universal property).** Let $u : \beta \to \gamma$ with $u \circ f = u \circ g$. Then there is a map $\bar u$ on the coequalizer with $\bar u(\mathrm{mk}(x)) = u(x)$.

*Proof.* The type is `Quot` of the relation `Function.Coequalizer.Rel f g`, whose only rule relates $f(x)$ and $g(x)$. The map $u$ respects this rule by the hypothesis. So the lift of $u$ to the quotient exists, and its value at the class of $x$ is $u(x)$ by definition. $\square$

The map is `Function.Coequalizer.desc` and the equation is `Function.Coequalizer.desc_mk`. Uniqueness of $\bar u$ follows from `Function.Coequalizer.mk_surjective`.

The module `Mathlib.Logic.Function.FiberPartition` defines `Function.Fiber f`, the type of the nonempty fibers $f^{-1}(\{z\})$ of a map $f$. A fiber has a chosen point `Function.Fiber.preimage f a` and a value `Function.Fiber.image f a`, and `Function.Fiber.mem_iff_eq_image` states that $y$ lies in a fiber exactly when $f(y)$ is its value.

The module `Mathlib.Logic.Function.DependsOn` defines `DependsOn f s` for a function $f$ of a family $x = (x_i)_{i \in \iota}$: the value $f(x)$ depends only on the coordinates $x_i$ with $i \in s$. The lemma `dependsOn_iff_exists_comp` states that $f$ factors through the restriction to $s$, and `DependsOn.mono` enlarges $s$. The module `Mathlib.Data.SubtypeNeLift` defines `Function.subtypeNeLift`, which extends a dependent function on $\{i \mid i \ne i_0\}$ by a value at $i_0$. The lemmas `Function.subtypeNeLift_self` and `Function.subtypeNeLift_of_neq` give its two cases.

The modules `Mathlib.Logic.Function.OfArity` and `Mathlib.Logic.Function.FromTypes` define the types of $n$-ary functions. The type `Function.OfArity α β n` is $\alpha \to \cdots \to \alpha \to \beta$ with $n$ arguments, and `Function.FromTypes p τ` is $p(0) \to \cdots \to p(n - 1) \to \tau$ for a family of types $p$. The recursion is by `Function.ofArity_succ` and `Function.fromTypes_succ`, and the equivalences such as `Function.fromTypes_cons_equiv` make the unfolding explicit. Both docstrings advise the form `(Fin n → α) → β` when it is enough.

#### Classes of operations and of composites

The module `Mathlib.Logic.OpClass` has three classes. `IsSymmOp op` states $\mathrm{op}(a, b) = \mathrm{op}(b, a)$ for an operation with values in another type. `LeftCommutative op` states $\mathrm{op}(a_1, \mathrm{op}(a_2, b)) = \mathrm{op}(a_2, \mathrm{op}(a_1, b))$, and `RightCommutative op` is the mirror form. A commutative and associative operation has both, by instance. These classes are the hypotheses that make a fold independent of the order: `List.Perm.foldr_eq` needs `LeftCommutative`, and `Multiset.foldr` takes it as an argument.

The module `Mathlib.Logic.Function.CompTypeclasses` defines the class `CompTriple φ ψ χ`, which records $\psi \circ \varphi = \chi$, and `CompTriple.IsId σ`, which records $\sigma = \mathrm{id}$. Instance search then finds the composite of two maps that index a structure. The composition `MulActionHom.comp` of equivariant maps uses it.

#### Common errors

1. A learner expects `f^[n + 1] = f ∘ f^[n]` to hold by `rfl`. The definition gives `f^[n] ∘ f`; the other form is `Function.iterate_succ'`.
2. A learner writes `Function.Semiconj f ga gb` with the maps in the wrong order. The statement is `f ∘ ga = gb ∘ f`: the map $f$ comes first, then the map on its domain, then the map on its codomain.
3. A learner tries to extract the constant value from `Function.IsConst f` with an empty domain. The value exists only when $\beta$ or $\alpha$ is nonempty; use `Function.isConst_iff_exists_eq_const`.

### Exercises

1. (A) Prove $f^{[m]} \circ f^{[n]} = f^{[n]} \circ f^{[m]}$ from `Function.iterate_add` and the commutativity of addition.
2. (A) Show that $\mathrm{Prod.swap} \circ \mathrm{diag} = \mathrm{diag}$, and state the result as an equation of `Function.prod`.
3. (B) Let $f$ be injective and let $f^{[m]}(a) = a$ and $f^{[n]}(a) = a$. Prove $f^{[\gcd(m, n)]}(a) = a$.
4. (B) Let $f : \alpha \to \beta$ be surjective and let $f$ semiconjugate an associative operation $g_a$ to $g_b$. Prove that $g_b$ is associative.
5. (B) Prove that a function $\mathbb{N} \to \mathbb{N}$ that commutes with $n \mapsto n + 1$ is of the form $n \mapsto n + c$.
6. (C) Construct an equivalence between `Function.Coequalizer f g` and the quotient of $\beta$ by the smallest equivalence relation that contains all pairs $(f(x), g(x))$.

### Reference

<?reference?>
