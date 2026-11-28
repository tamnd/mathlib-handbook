---
title: Partial values, partial functions and options
kind: api
modules:
  - Mathlib.Data.Part
  - Mathlib.Data.PFun
  - Mathlib.Data.Option.Basic
  - Mathlib.Data.Option.Defs
  - Mathlib.Data.Option.NAry
  - Mathlib.Data.Erased
explains:
  E2: [Part.mem_unique, Part.ext, PFun.core_eq, PFun.preimage_comp, Option.map₂_eq_none_iff, Erased.nonempty_iff]
  E1: auto
families: []
requires: [V01.C02, V01.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Partial values, partial functions and options

### Overview

The previous section showed the main convention of Mathlib for an operation that is not defined everywhere: the operation is made total, and it takes a junk value outside its domain. So $x / 0 = 0$ and $\sqrt{-1} = 0$. This convention is the right one for algebra and analysis. It is not the right one for every subject. In computability, a program can fail to halt, and its "value" must record this. In the theory of partial maps, the domain of a map is part of the data. For these subjects, Mathlib has types that record the absence of a value.

This section treats four such types. The type `Option α` adds one new element `none` to $\alpha$, and its absence of value is decidable. The type `Part α` of *partial values* carries a proposition, its domain, and a value under a proof of the domain. The domain need not be decidable. The type `α →. β` of *partial functions* is the function type `α → Part β`. The type `Erased α` holds a value of $\alpha$ that proofs can use and compiled code cannot. The modules are `Mathlib.Data.Part`, `Mathlib.Data.PFun`, `Mathlib.Data.Option.Basic`, `Mathlib.Data.Option.Defs`, `Mathlib.Data.Option.NAry` and `Mathlib.Data.Erased`. The reader needs the sets of Chapter 2 and the functions and equivalences of Chapter 3.

### The library around it

#### Partial values

The structure `Part α` has two fields: a proposition `Dom` and a function `get : Dom → α`. A term `o : Part α` is *defined* when `o.Dom` holds, and then `o.get h` is its value. The two basic partial values are `Part.some a`, with the domain `True` and the value $a$, and `Part.none`, with the domain `False`. The relation `a ∈ o` (from `Part.Mem`) means that `o` is defined with the value $a$: the lemma `Part.mem_eq` states `(a ∈ o) = ∃ h : o.Dom, o.get h = a`. Most lemmas of the library state facts with `∈`, not with `get`. The lemmas `Part.get_eq_iff_mem`, `Part.get_mem` and `Part.get_eq_of_mem` translate between the two forms.

**Theorem (A partial value has at most one value).** If $a \in o$ and $b \in o$, then $a = b$.

*Proof.* By `Part.mem_eq`, there are proofs $h, h'$ of `o.Dom` with `o.get h = a` and `o.get h' = b`. The proofs $h$ and $h'$ are equal by proof irrelevance. So $a = o.\mathrm{get}\ h = o.\mathrm{get}\ h' = b$. $\square$

This is `Part.mem_unique`. The lemma `Part.subsingleton` states the same fact as `{a | a ∈ o}.Subsingleton`. So `Part α` is the type of subsingleton subsets of $\alpha$, in another form.

**Theorem (Extensionality).** Two partial values $o, p$ are equal when $a \in o \leftrightarrow a \in p$ for every $a$.

*Proof.* Assume $o.\mathrm{Dom}$. Then $o.\mathrm{get}\ h \in o$, so it is in $p$, and $p$ is defined. The converse is the same, so the two domains are equivalent. For proofs $h_1, h_2$ of the domains, the value $o.\mathrm{get}\ h_1$ is in $p$, and the previous theorem gives $o.\mathrm{get}\ h_1 = p.\mathrm{get}\ h_2$. The lemma `Part.ext'` then gives $o = p$. $\square$

This is `Part.ext`, and `Part.ext_iff` is its equivalence form. The lemma `Part.ext'` is the form with domains and values. The lemmas `Part.mem_some_iff`, `Part.notMem_none`, `Part.some_injective`, `Part.some_ne_none` and `Part.ne_none_iff` give the basic computations. The induction principle `Part.induction_on` proves a statement for `Part.none` and for each `Part.some a`. It uses classical logic, because a domain need not be decidable.

`Part` is a monad (`Part.instMonad`, `Part.instLawfulMonad`). The bind `Part.bind o f` is defined when `o` is defined with a value $a$ and `f a` is defined. The lemma `Part.bind_dom` states this, and `Part.mem_bind_iff` gives $b \in o \mathbin{>\!\!>\!\!=} f \leftrightarrow \exists a \in o,\ b \in f(a)$. The map `Part.map` keeps the domain (`Part.map_Dom`). The lemmas `Part.bind_some`, `Part.bind_none`, `Part.bind_assoc`, `Part.map_some`, `Part.map_none` and `Part.map_map` are the monad laws in the language of `Part`. The function `Part.assert p f` is defined when $p$ holds and `f h` is defined: see `Part.mem_assert_iff`. The function `Part.restrict` shrinks the domain.

The partial values carry an order (`Part.instPartialOrder`): $x \leq y$ when every value of $x$ is a value of $y$. The least element is `Part.none` (`Part.instOrderBot`). In this order, a partial value is either undefined or maximal. The lemma `Part.le_total_of_le_of_le` states that two lower bounds of the same $z$ are comparable.

The arithmetic operations lift to `Part α` through the monad. There is a family of instances `Part.instAdd`, `Part.instMul`, `Part.instSub`, `Part.instDiv`, `Part.instNeg`, `Part.instInv` and others, and each operation has the same five lemmas. For addition they are:

| Lean name | Statement |
|---|---|
| `Part.add_def` | $a + b$ is the bind of $a$ and $b$ under $+$ |
| `Part.some_add_some` | `Part.some a + Part.some b = Part.some (a + b)` |
| `Part.add_mem_add` | $m_a \in a$ and $m_b \in b$ give $m_a + m_b \in a + b$ |
| `Part.left_dom_of_add_dom` | if $a + b$ is defined, then $a$ is defined |
| `Part.add_get_eq` | the value of $a + b$ is the sum of the values |

The names for the other operations follow the pattern: `Part.some_mul_some`, `Part.mul_mem_mul`, `Part.right_dom_of_div_dom`, `Part.sub_get_eq`, and so on.

`Part` and `Option` are close. The coercion `Part.ofOption` sends `Option α` to `Part α` (`Part.instCoeOption`), with the lemmas `Part.coe_some`, `Part.coe_none` and `Part.mem_coe`. In the other direction, `Part.toOption o` needs an instance `Decidable o.Dom`, because it must test the domain. The lemmas `Part.to_ofOption`, `Part.of_toOption` and `Part.mem_toOption` show that the two maps are inverse. Without the decidability, the equivalence `Part.equivOption : Part α ≃ Option α` still exists, but it is noncomputable: it decides the domain by classical logic. The function `Part.getOrElse` returns a default value outside the domain. The function `Part.unwrap` takes the value without a proof of the domain. It is `unsafe` and has no place in proofs.

#### Partial functions

The type `PFun α β`, with the notation `α →. β`, is `α → Part β`. Its domain `PFun.Dom f` is the set $\{x \mid (f\,x).\mathrm{Dom}\}$, and `PFun.mem_dom` states $x \in \mathrm{Dom}\, f \leftrightarrow \exists y,\ y \in f\,x$. The evaluation `PFun.fn f a h` takes a proof `h` that $a$ is in the domain. The function `PFun.asSubtype f` is the total function on the subtype of the domain. The equivalence `PFun.equivSubtype` identifies `α →. β` with the pairs $(p, g)$ of a predicate $p$ on $\alpha$ and a function $g : \{x \mid p\,x\} \to \beta$. This is the textbook definition of a partial function: a subset with a function on it. Extensionality is `PFun.ext`.

A total function is a partial function with the full domain. The coercion is `PFun.lift`, with `PFun.coe_val : ↑f a = Part.some (f a)`, `PFun.dom_coe` and `PFun.lift_injective`. The function `PFun.res f s` restricts a total function to a set $s$. The function `PFun.restrict` shrinks the domain of a partial function. The function `PFun.toSubtype p f` is defined at $a$ when $p\,(f\,a)$ holds.

A partial function has two preimages of a set $s \subseteq \beta$. The *preimage* `PFun.preimage f s` is $\{x \mid \exists y \in s,\ y \in f\,x\}$: the points of the domain whose value is in $s$. The *core* `PFun.core f s` is $\{x \mid \forall y \in f\,x,\ y \in s\}$: the points where $f$ is undefined or has a value in $s$. The two notions agree for total functions (`PFun.coe_preimage`, `PFun.core_restrict`). In general they differ on the complement of the domain.

**Theorem (Core and preimage).** For $f : \alpha \rightharpoonup \beta$ and $s \subseteq \beta$, $\mathrm{core}_f(s) = f^{-1}(s) \cup (\mathrm{Dom}\, f)^c$.

*Proof.* Let $x \in \alpha$. If $x \in \mathrm{Dom}\, f$, then $f\,x$ has exactly one value $y$, by `Part.mem_unique`. Then $x \in \mathrm{core}_f(s)$ means $y \in s$, and this is $x \in f^{-1}(s)$. If $x \notin \mathrm{Dom}\, f$, then $f\,x$ has no value, so $x \in \mathrm{core}_f(s)$ holds vacuously, and $x$ is in the complement of the domain. $\square$

This is `PFun.core_eq`. The lemma `PFun.preimage_eq` states the dual form $f^{-1}(s) = \mathrm{core}_f(s) \cap \mathrm{Dom}\, f$. The preimage commutes with unions and intersections (`PFun.preimage_union`, `PFun.preimage_inter`), and the core commutes with intersections (`PFun.core_inter`). The image `PFun.image f s` and the range `PFun.ran f` are the other set operations. The graph is `PFun.graph f : Set (α × β)`, and `PFun.graph'` is the same graph as a `SetRel α β`, the relations of Chapter 3.

Partial functions compose. The composite `PFun.comp f g` sends $a$ to the bind of $g\,a$ with $f$ (`PFun.comp_apply`). The identity is `PFun.id`, and `PFun.comp_assoc`, `PFun.id_comp` and `PFun.comp_id` are the category laws. The domain of a composite is `PFun.dom_comp : (f.comp g).Dom = g.preimage f.Dom`.

**Theorem (Preimage of a composite).** For $g : \alpha \rightharpoonup \beta$, $f : \beta \rightharpoonup \gamma$ and $s \subseteq \gamma$, $(f \circ g)^{-1}(s) = g^{-1}(f^{-1}(s))$.

*Proof.* By `Part.mem_bind_iff`, $c \in (f \circ g)(x)$ holds if and only if $c \in f\,b$ for some $b \in g\,x$. So $x$ is in the left side if and only if $\exists c \in s,\ \exists b \in g\,x,\ c \in f\,b$. Exchange the two existential quantifiers: this is $\exists b \in g\,x,\ \exists c \in s,\ c \in f\,b$, which is $\exists b \in g\,x,\ b \in f^{-1}(s)$. This is the right side. $\square$

This is `PFun.preimage_comp`. The products are `PFun.prodLift f g`, defined where both $f$ and $g$ are defined, and `PFun.prodMap f g` on $\alpha \times \beta$. For each fixed $\alpha$, the type `α →. β` is a monad in $\beta$ (`PFun.monad`, `PFun.lawfulMonad`).

The function `PFun.fix` turns a partial function $f : \alpha \rightharpoonup \beta \oplus \alpha$ into a partial function $\alpha \rightharpoonup \beta$. It is the loop "apply $f$; on a value $\mathrm{inr}\ a'$ continue at $a'$; on a value $\mathrm{inl}\ b$ stop with $b$". The value is defined when the loop stops. The lemma `PFun.mem_fix_iff` states the one-step unfolding, `PFun.fix_stop` and `PFun.fix_fwd` are its two halves, and `PFun.fixInduction` is the induction principle on a terminating run. The computability library uses this type: a partial recursive function is a term of `ℕ →. ℕ` with the property `Nat.Partrec`, and `Nat.rfind` is the unbounded search. The function `PFun.evalOpt` turns a partial function with a decidable domain into a function to `Option β`.

#### Options

The type `Option α` is defined in the core library, with the constructors `some` and `none`. The module `Mathlib.Data.Option.Basic` adds lemmas. The lemmas `Option.some_injective`, `Option.map_injective'`, `Option.map_inj` and `Option.mem_map_of_injective` concern injectivity. The lemmas `Option.mem_map`, `Option.forall_mem_map` and `Option.exists_mem_map` translate a statement about `Option.map f o` into a statement about `o`. The membership `a ∈ o` means `o = some a`, and `Option.Mem.leftUnique` states that an option holds at most one value. The eliminator `Option.casesOn'` and its lemmas `Option.casesOn'_some` and `Option.casesOn'_none` give a value in both cases, and `Option.casesOn'_eq_elim` reduces it to the core eliminator. The module `Mathlib.Data.Option.Defs` has `Option.elim'`, the eliminator with the option as the last argument, so that `Option.elim' b f` is a function on `Option α`. The lemmas `Option.elim'_none`, `Option.elim'_some` and `Option.elim'_eq_elim` describe it. It also defines `Option.traverse`. The lemma `Option.choice_eq_none` states that the canonical option of an empty type is `none`.

The module `Mathlib.Data.Option.NAry` defines the binary map `Option.map₂ f a b`. It is `some (f x y)` when $a = \mathrm{some}\ x$ and $b = \mathrm{some}\ y$, and `none` otherwise.

**Theorem.** $\mathrm{map}_2\, f\, a\, b = \mathrm{none}$ if and only if $a = \mathrm{none}$ or $b = \mathrm{none}$.

*Proof.* Split on $a$ and $b$. If both are `some`, the left side is `some (f x y)`, which is not `none`, and the right side is false. In the three other cases both sides are true, by `Option.map₂_none_left` and `Option.map₂_none_right`. $\square$

This is `Option.map₂_eq_none_iff`, and `Option.map₂_eq_some_iff` is the companion. The rest of the module copies the binary-image API of sets (`Set.image2`) and finsets (`Finset.image₂`): `Option.map₂_comm` and `Option.map₂_swap` for a symmetric $f$, `Option.map₂_assoc`, `Option.map₂_left_comm` and `Option.map₂_right_comm` for associativity, the distributivity family `Option.map_map₂_distrib`, `Option.map_map₂_distrib_left` and `Option.map_map₂_antidistrib`, and the identity laws `Option.map₂_left_identity` and `Option.map₂_right_identity`. The names follow one pattern in the three modules, so a proof about `Option.map₂` often copies a proof about `Set.image2`. The main use is the pointwise operations on intervals.

#### Erased values

The type `Erased α` is defined in the core library as the type of predicates $s$ on $\alpha$ of the form $s = (a = \cdot)$ for some $a$. It holds one value of $\alpha$, but the value is hidden from compiled code. The core functions `Erased.mk` and `Erased.out` are inverse, and `Erased.out` is noncomputable. The module `Mathlib.Data.Erased` adds the equivalence `Erased.equiv : Erased α ≃ α`, the monad structure (`Erased.bind`, `Erased.map`, `Erased.join`, with `Erased.bind_eq_out`, `Erased.map_out` and `Erased.join_eq_out`), and `Erased.choice`, which makes an erased value from a proof of `Nonempty α`.

**Theorem.** `Erased α` is nonempty if and only if $\alpha$ is nonempty.

*Proof.* From $e : \mathrm{Erased}\ \alpha$, the term `e.out` is an element of $\alpha$. From $a : \alpha$, the term `Erased.mk a` is an element of `Erased α`. $\square$

This is `Erased.nonempty_iff`. The point of `Erased.choice` is that `Classical.choice` cannot give data to compiled code, but it can give an erased value. A program can then carry a chosen element in a field that proofs use. The lemma `Erased.out_proof` extracts a proof from an erased proof.

#### Common errors

1. A learner writes `o.get h` in a statement and then cannot rewrite with a lemma in the form `a ∈ o`. Convert with `Part.get_eq_iff_mem` first, or state the goal with `∈`.
2. A learner uses `Part.toOption` and Lean cannot find the instance `Decidable o.Dom`. A domain such as "the program halts" is not decidable. Use `Part.equivOption` in a proof, or add `open Classical`.
3. A learner confuses `PFun.preimage` with `PFun.core`. The preimage contains only points of the domain. The core also contains every point outside the domain.

### Exercises

1. (A) Prove that `Part.some a + Part.none = Part.none` for $a : \mathbb{N}$. Which lemma about the domain of a sum gives the shortest proof?
2. (A) Prove that $\mathrm{Dom}\,(\mathrm{PFun.res}\ f\ s) = s$ for a total function $f$ and a set $s$.
3. (B) Prove that $x \leq y$ in `Part α` holds if and only if $x = \mathrm{none}$ or $x = y$.
4. (B) Prove that $f^{-1}(\beta) = \mathrm{Dom}\, f$ and $\mathrm{core}_f(\emptyset) = (\mathrm{Dom}\, f)^c$ for a partial function $f : \alpha \rightharpoonup \beta$.
5. (B) Let $f : \mathbb{N} \rightharpoonup \mathbb{N} \oplus \mathbb{N}$ send $n$ to $\mathrm{inl}\ n$ when $n$ is even and to $\mathrm{inr}\ (n + 1)$ when $n$ is odd. Compute `PFun.fix f` at every $n$.
6. (C) Construct the equivalence between `α →. β` and the type of relations $R \subseteq \alpha \times \beta$ with $R(x, y) \land R(x, y') \to y = y'$. Use `PFun.graph'` in one direction.

### Reference

<?reference?>
