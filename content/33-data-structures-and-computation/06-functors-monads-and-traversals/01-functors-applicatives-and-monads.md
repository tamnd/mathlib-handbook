---
title: Functors, applicatives and monads
kind: theory
modules:
  - Mathlib.Control.Basic
  - Mathlib.Control.Applicative
  - Mathlib.Control.Functor
  - Mathlib.Control.Combinators
  - Mathlib.Control.Lawful
  - Mathlib.Control.Monad.Basic
  - Mathlib.Control.Monad.Cont
  - Mathlib.Control.Monad.Writer
  - Mathlib.Control.ULift
  - Mathlib.Control.ULiftable
  - Mathlib.Control.EquivFunctor
  - Mathlib.Control.EquivFunctor.Instances
  - Mathlib.Control.Bifunctor
explains:
  E3: [Functor.Comp, Functor.Comp.lawfulFunctor, Functor.Comp.instLawfulApplicativeComp, map_seq, seq_map_assoc, joinM, joinM_pure, joinM_map_pure, fish_assoc, Sum.bind, CommApplicative, ContT, MonadCont, LawfulMonadCont, ContT.run_callCC, WriterT, WriterT.run_bind, MonadWriter, ULiftable, ULiftable.down_up, EquivFunctor, EquivFunctor.mapEquiv, Bifunctor, LawfulBifunctor, Bifunctor.fst_snd]
  E2: [Functor.Const, Functor.AddConst, Functor.Liftp, Functor.Liftr, Functor.supp, Functor.ext, Applicative.ext, CommApplicative.commutative_map, fish_pure, fish_pipe, joinM_map_joinM, zipWithM, List.mapAccumLM, condM, map_eq_bind_pure_comp, StateT.eval, StateT.run_mapConst, Cont, LawfulMonadCont.callCC_bind_left, WriterT.monad, WriterT.run_tell, ULift.bind, ULiftable.up, ULiftable.up_down, EquivFunctor.ofLawfulFunctor, EquivFunctor.mapEquiv_trans, EquivFunctor.mapEquiv.injective, EquivFunctorPerm, EquivFunctorFinset, Prod.bifunctor, Sum.bifunctor, Bifunctor.functor, seq_bind_eq, Functor.Comp.seq_assoc, Sum.instLawfulMonad_mathlib, instCommApplicativeId]
  E1: auto
families: []
requires: [V01.C04, V03.C02, V24.C06, V33.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Functors, applicatives and monads

### Overview

A program often computes a value inside a context: a value that can be absent (`Option`), a list of possible values (`List`), a value with an error (`Except` or `Sum`), a value that reads or changes a state (`StateT`), or a value with a log (`WriterT`). The classes `Functor`, `Applicative` and `Monad` give one interface to all these contexts. A functor lets a pure function act inside the context. An applicative functor also combines two independent computations. A monad lets the second computation depend on the result of the first.

The classes and their laws (`LawfulFunctor`, `LawfulApplicative`, `LawfulMonad`) are in the core of Lean. Mathlib adds lemmas that follow from the laws, combinators such as `joinM` and the Kleisli arrow `>=>`, lawful instances for `Sum`, the composition of two functors, the continuation monad `ContT` and the writer monad `WriterT`. It also adds three structures that are less common in programming texts: `ULiftable` to move a functor between universes, `EquivFunctor` for type constructors that act only on equivalences, and `Bifunctor` for type constructors with two arguments.

### Definitions

**Definition (Functor and its laws).** A functor is a type constructor `F : Type u → Type v` with a map $\mathrm{map} \colon (\alpha \to \beta) \to F\,\alpha \to F\,\beta$, written `f <$> x`. It is lawful if $\mathrm{id} \mathbin{<\$>} x = x$ and $(g \circ f) \mathbin{<\$>} x = g \mathbin{<\$>} (f \mathbin{<\$>} x)$. For `List`, the map is `List.map`. For `Option`, it maps `some a` to `some (f a)` and keeps `none`.

**Definition (Applicative functor).** An applicative functor adds $\mathrm{pure} \colon \alpha \to F\,\alpha$ and $\mathrm{seq} \colon F(\alpha \to \beta) \to F\,\alpha \to F\,\beta$, written `g <*> x`. The lawful version asks for four laws: $\mathrm{pure}\,g \mathbin{<*>} x = g \mathbin{<\$>} x$, $g \mathbin{<\$>} \mathrm{pure}\,a = \mathrm{pure}(g\,a)$, $h \mathbin{<*>} \mathrm{pure}\,a = (\lambda k.\, k\,a) \mathbin{<\$>} h$, and the associativity law $h \mathbin{<*>} (g \mathbin{<*>} x) = ((\circ) \mathbin{<\$>} h \mathbin{<*>} g) \mathbin{<*>} x$.

**Definition (Monad).** A monad adds $\mathrm{bind} \colon F\,\alpha \to (\alpha \to F\,\beta) \to F\,\beta$, written `x >>= f`. The laws are $\mathrm{pure}\,a \mathbin{>>=} f = f\,a$, $x \mathbin{>>=} \mathrm{pure} = x$ and $(x \mathbin{>>=} f) \mathbin{>>=} g = x \mathbin{>>=} (\lambda a.\, f\,a \mathbin{>>=} g)$, together with the agreement of `map` and `seq` with `bind`. The lemma `map_eq_bind_pure_comp` states the first agreement: $f \mathbin{<\$>} x = x \mathbin{>>=} \mathrm{pure} \circ f$.

**Definition (Join and Kleisli arrow).** `joinM a = a >>= id` flattens $F(F\,\alpha)$ to $F\,\alpha$. For $f \colon \alpha \to F\,\beta$ and $g \colon \beta \to F\,\gamma$, the Kleisli composite is $(f \mathbin{>=>} g)\,x = f\,x \mathbin{>>=} g$.

**Definition (Commutative applicative).** An applicative functor is commutative (`CommApplicative`) if the order of two independent effects does not change the result: $\mathrm{Prod.mk} \mathbin{<\$>} a \mathbin{<*>} b = (\lambda\, b\,a.\, (a, b)) \mathbin{<\$>} b \mathbin{<*>} a$.

**Definition (Composition of functors).** For functors $F$ and $G$, `Functor.Comp F G α` is $F(G\,\alpha)$. The map is $\mathrm{map}_F(\mathrm{map}_G\,f)$, `pure` is $\mathrm{pure}_F \circ \mathrm{pure}_G$, and `seq` applies $\mathrm{seq}_G$ inside $F$ with $\mathrm{seq}_F$.

**Definition (Continuation monad).** `ContT r m α` is $(\alpha \to m\,r) \to m\,r$: a computation that receives the rest of the program, its continuation $k$, and produces the final answer. The operations are $\mathrm{pure}\,a = \lambda k.\, k\,a$ and $(x \mathbin{>>=} f) = \lambda k.\, x\,(\lambda a.\, f\,a\,k)$. `Cont r` is `ContT r Id`. The class `MonadCont` has `callCC : (Label α m β → m α) → m α`, and `goto l a` jumps to the label $l$ with the value $a$. In `ContT`, $\mathrm{callCC}\,f = \lambda k.\, f\,\ell\,k$ with $\ell = \lambda a.\, \lambda \_.\, k\,a$: the label forgets its own continuation and returns to $k$.

**Definition (Writer monad).** `WriterT ω M α` is $M(\alpha \times \omega)$, a computation with a log in $\omega$. For a neutral element $e$ and an operation $\cdot$ on $\omega$, `WriterT.monad e (·)` defines $\mathrm{pure}\,a = \mathrm{pure}_M(a, e)$ and $$x \mathbin{>>=} f = x \mathbin{>>=_M} \lambda (a, w_1).\, (\lambda (b, w_2).\, (b, w_1 \cdot w_2)) \mathbin{<\$>} f\,a.$$ The class `MonadWriter ω` has `tell w`, which adds $w$ to the log, `listen` and `pass`.

**Definition (ULiftable).** `ULiftable f g` gives for each equivalence $\alpha \simeq \beta$ an equivalence $f\,\alpha \simeq g\,\beta$ (the field `congr`). With $\alpha \simeq \mathrm{ULift}\,\alpha$ it gives `up : f α → g (ULift α)` and `down` in the other direction.

**Definition (Equivalence functor).** `EquivFunctor f` has $\mathrm{map} \colon (\alpha \simeq \beta) \to f\,\alpha \to f\,\beta$ with $\mathrm{map}(\mathrm{refl}) = \mathrm{id}$ and $\mathrm{map}(k \mathbin{.trans} h) = \mathrm{map}\,h \circ \mathrm{map}\,k$. Only equivalences act, not all functions.

**Definition (Bifunctor).** `Bifunctor F` has $\mathrm{bimap} \colon (\alpha \to \alpha') \to (\beta \to \beta') \to F\,\alpha\,\beta \to F\,\alpha'\,\beta'$. It is lawful if $\mathrm{bimap}\,\mathrm{id}\,\mathrm{id} = \mathrm{id}$ and $\mathrm{bimap}\,f_0\,f_1 \circ \mathrm{bimap}\,g_0\,g_1 = \mathrm{bimap}\,(f_0 \circ g_0)\,(f_1 \circ g_1)$. One-sided maps are $\mathrm{fst}\,f = \mathrm{bimap}\,f\,\mathrm{id}$ and $\mathrm{snd}\,f = \mathrm{bimap}\,\mathrm{id}\,f$.

### Theorems and proofs

**Proposition (Map over seq).** In a lawful applicative functor, $f \mathbin{<\$>} (x \mathbin{<*>} y) = ((f \circ \cdot) \mathbin{<\$>} x) \mathbin{<*>} y$ and $x \mathbin{<*>} (f \mathbin{<\$>} y) = ((\cdot \circ f) \mathbin{<\$>} x) \mathbin{<*>} y$.

*Proof.* For the first identity, write the map as a seq with pure, then use associativity, then the map of a pure value, then the first law again: $$f \mathbin{<\$>} (x \mathbin{<*>} y) = \mathrm{pure}\,f \mathbin{<*>} (x \mathbin{<*>} y) = ((\circ) \mathbin{<\$>} \mathrm{pure}\,f \mathbin{<*>} x) \mathbin{<*>} y = (\mathrm{pure}(f \circ \cdot) \mathbin{<*>} x) \mathbin{<*>} y = ((f \circ \cdot) \mathbin{<\$>} x) \mathbin{<*>} y.$$ For the second identity, $f \mathbin{<\$>} y = \mathrm{pure}\,f \mathbin{<*>} y$, and associativity gives $x \mathbin{<*>} (\mathrm{pure}\,f \mathbin{<*>} y) = ((\circ) \mathbin{<\$>} x \mathbin{<*>} \mathrm{pure}\,f) \mathbin{<*>} y$. The law for a pure argument turns $(\circ) \mathbin{<\$>} x \mathbin{<*>} \mathrm{pure}\,f$ into $(\lambda k.\, k\,f) \mathbin{<\$>} ((\circ) \mathbin{<\$>} x)$, and the composition law of the functor makes it $(\lambda h.\, h \circ f) \mathbin{<\$>} x$. $\square$

These are `map_seq` and `seq_map_assoc`. They let `simp` move every map to the left end of a chain of `<*>`.

**Proposition (Join laws).** In a lawful monad, $\mathrm{joinM}(\mathrm{pure}\,a) = a$, $\mathrm{joinM}(\mathrm{pure} \mathbin{<\$>} a) = a$ and $\mathrm{joinM}(\mathrm{joinM} \mathbin{<\$>} a) = \mathrm{joinM}(\mathrm{joinM}\,a)$.

*Proof.* The first identity is $\mathrm{pure}\,a \mathbin{>>=} \mathrm{id} = \mathrm{id}\,a = a$ by the left unit law. For the second, $f \mathbin{<\$>} x \mathbin{>>=} g = x \mathbin{>>=} g \circ f$ (this is `seq_bind_eq`, proved from `map_eq_bind_pure_comp` and associativity). So $(\mathrm{pure} \mathbin{<\$>} a) \mathbin{>>=} \mathrm{id} = a \mathbin{>>=} \mathrm{pure} = a$ by the right unit law. For the third, the same lemma gives $(\mathrm{joinM} \mathbin{<\$>} a) \mathbin{>>=} \mathrm{id} = a \mathbin{>>=} \mathrm{joinM} = a \mathbin{>>=} (\lambda x.\, x \mathbin{>>=} \mathrm{id})$. Associativity gives $(a \mathbin{>>=} \mathrm{id}) \mathbin{>>=} \mathrm{id} = a \mathbin{>>=} (\lambda x.\, \mathrm{id}\,x \mathbin{>>=} \mathrm{id})$, which is the same term. $\square$

**Proposition (Kleisli category).** In a lawful monad, $f \mathbin{>=>} \mathrm{pure} = f$, $\mathrm{pure} \mathbin{>=>} f = f$ and $(f \mathbin{>=>} g) \mathbin{>=>} h = f \mathbin{>=>} (g \mathbin{>=>} h)$.

*Proof.* Evaluate at $x$. The first is $f\,x \mathbin{>>=} \mathrm{pure} = f\,x$, the second is $\mathrm{pure}\,x \mathbin{>>=} f = f\,x$. For the third, the left side at $x$ is $(f\,x \mathbin{>>=} g) \mathbin{>>=} h$ and the right side is $f\,x \mathbin{>>=} (\lambda y.\, g\,y \mathbin{>>=} h)$. These are equal by associativity. Function extensionality ends the proof. $\square$

So the monad laws say that types with the arrows $\alpha \to F\,\beta$ form a category. Lemmas `fish_pure`, `fish_pipe` and `fish_assoc` are the three identities.

**Proposition (The sum monad).** For a fixed type $e$, `Sum e` with $\mathrm{pure} = \mathrm{inr}$ and $\mathrm{bind}(\mathrm{inl}\,u, f) = \mathrm{inl}\,u$, $\mathrm{bind}(\mathrm{inr}\,a, f) = f\,a$ is a lawful monad.

*Proof.* Left unit: $\mathrm{inr}\,a \mathbin{>>=} f = f\,a$ by the second clause. Right unit, by cases on $x$: $\mathrm{inl}\,u \mathbin{>>=} \mathrm{inr} = \mathrm{inl}\,u$, and $\mathrm{inr}\,a \mathbin{>>=} \mathrm{inr} = \mathrm{inr}\,a$. Associativity, by cases on $x$: for $x = \mathrm{inl}\,u$ both sides are $\mathrm{inl}\,u$, and for $x = \mathrm{inr}\,a$ both sides are $f\,a \mathbin{>>=} g$. The map of `Sum e` is `Sum.map id`, and the same case split shows that it agrees with $x \mathbin{>>=} \mathrm{inr} \circ f$. $\square$

The value $\mathrm{inl}\,u$ is an error that stops the rest of the computation. This is the monad `Except e` under another name.

**Theorem (Composition of applicative functors).** If $F$ and $G$ are lawful applicative functors, then `Functor.Comp F G` is a lawful applicative functor. If both are commutative, so is the composite.

*Proof.* The functor laws: $\mathrm{map}_F(\mathrm{map}_G\,\mathrm{id})\,x = \mathrm{map}_F\,\mathrm{id}\,x = x$, and $\mathrm{map}_F(\mathrm{map}_G(g \circ f)) = \mathrm{map}_F(\mathrm{map}_G\,g \circ \mathrm{map}_G\,f) = \mathrm{map}_F(\mathrm{map}_G\,g) \circ \mathrm{map}_F(\mathrm{map}_G\,f)$. The seq of the composite is $h \mathbin{<*>} x = (\mathrm{seq}_G) \mathbin{<\$>_F} h \mathbin{<*>_F} x$. For the law of a pure function, $\mathrm{pure}_F(\mathrm{pure}_G\,g) \mathbin{<*>} x = (\mathrm{pure}_G\,g \mathbin{<*>_G} \cdot) \mathbin{<\$>_F} x = (g \mathbin{<\$>_G} \cdot) \mathbin{<\$>_F} x$, which is the map of the composite. The law for a pure argument has the same form. For associativity, push all maps to the left in $F$ with the previous proposition. Each side becomes one map in $F$ of a function on three arguments of $G$, applied to $h$, $g$ and $x$ by $\mathrm{seq}_F$. The two functions agree by associativity in $G$. For commutativity, the identity for `Prod.mk` in the composite reduces in the same way to the commutativity in $G$ inside a swap of the two arguments in $F$. $\square$

**Proposition (Writer is lawful over a monoid).** If $(\omega, \cdot, 1)$ is a monoid and $M$ is a lawful monad, then `WriterT ω M` with neutral element $1$ is a lawful monad.

*Proof.* Take $M = \mathrm{Id}$ first. Left unit: $\mathrm{pure}\,a \mathbin{>>=} f$ is $(b, 1 \cdot w)$ where $f\,a = (b, w)$, and $1 \cdot w = w$. Right unit: $(a, w) \mathbin{>>=} \mathrm{pure} = (a, w \cdot 1) = (a, w)$. Associativity: let $x = (a, w_1)$, $f\,a = (b, w_2)$ and $g\,b = (c, w_3)$. The left side is $(c, (w_1 w_2) w_3)$ and the right side is $(c, w_1 (w_2 w_3))$. For a general $M$, the same three computations happen under the bind of $M$, and the laws of $M$ move the binds into the right order. $\square$

So each monad law of the writer is a monoid law of the log. The library provides the lawful instance only under `[Monoid ω]`.

**Proposition (Equivalence functors map equivalences).** If $f$ is an `EquivFunctor`, then for $e \colon \alpha \simeq \beta$ the maps $\mathrm{map}\,e$ and $\mathrm{map}\,e^{-1}$ are inverse, so they form an equivalence $f\,\alpha \simeq f\,\beta$ (`mapEquiv f e`). The map $e \mapsto \mathrm{mapEquiv}\,f\,e$ respects composition.

*Proof.* $\mathrm{map}\,e^{-1}(\mathrm{map}\,e\,x) = \mathrm{map}(e \mathbin{.trans} e^{-1})\,x = \mathrm{map}(\mathrm{refl})\,x = x$ by the two laws. The other order is the same with $e$ and $e^{-1}$ exchanged. Compatibility with composition is the second law. $\square$

**Proposition (Bifunctor lemmas).** In a lawful bifunctor, $\mathrm{fst}\,f\,(\mathrm{snd}\,f'\,x) = \mathrm{bimap}\,f\,f'\,x = \mathrm{snd}\,f'\,(\mathrm{fst}\,f\,x)$.

*Proof.* $\mathrm{bimap}\,f\,\mathrm{id}\,(\mathrm{bimap}\,\mathrm{id}\,f'\,x) = \mathrm{bimap}\,(f \circ \mathrm{id})\,(\mathrm{id} \circ f')\,x = \mathrm{bimap}\,f\,f'\,x$ by the composition law. The other order is symmetric. $\square$

### Examples

**Example (The list monad).** Mathlib makes `List` a lawful monad with $\mathrm{pure}\,a = [a]$ and $l \mathbin{>>=} f = \mathrm{flatMap}\,f\,l$. Then $[1, 2] \mathbin{>>=} (\lambda n.\, [n, 10 n]) = [1, 10] \mathbin{+\!\!+} [2, 20] = [1, 10, 2, 20]$. The join flattens: $\mathrm{joinM}\,[[1], [], [2, 3]] = [1, 2, 3]$.

**Counterexample (List is not commutative).** In the list applicative, $\mathrm{Prod.mk} \mathbin{<\$>} [1, 2] \mathbin{<*>} [a, b] = [(1, a), (1, b), (2, a), (2, b)]$, since the first list is the outer loop. The other side of the commutativity law is $(\lambda\, y\,x.\, (x, y)) \mathbin{<\$>} [a, b] \mathbin{<*>} [1, 2] = [(1, a), (2, a), (1, b), (2, b)]$. The two lists have the same elements in a different order, so `List` is not a `CommApplicative`. `Option`, `Set` and `Id` have no order of results, and `Set` and `Id` have instances (`Set.instCommApplicative`, `instCommApplicativeId`).

**Example (Escape with callCC).** In `ContT Nat Id`, take $f\,\ell = \mathrm{goto}\,\ell\,5 \mathbin{>>=} (\lambda \_.\, \mathrm{pure}\,7)$ and run $\mathrm{callCC}\,f$ with $k = \mathrm{id}$. By `ContT.run_callCC`, the run is $f\,\ell\,k$ with $\ell\,a = \lambda \_.\, k\,a$. The bind gives $(\mathrm{goto}\,\ell\,5)(\lambda i.\, \mathrm{pure}\,7\,k) = k\,5 = 5$. The continuation after the jump is dropped, so the answer is $5$ and not $7$.

```lean
open MonadCont in
example : ContT.run (callCC (fun k => do let _ : Nat ← goto k 5; pure 7) : ContT Nat Id Nat) id = 5 := rfl
```

**Example (A log of strings).** In `Writer (List String)`, the program `tell ["a"]; tell ["b"]; pure 3` has the value $(3, [\text{"a"}, \text{"b"}])$. By `run_tell`, each `tell w` is $(\langle\rangle, w)$, and by `run_bind` the logs are appended in order: $[\text{"a"}] \mathbin{+\!\!+} ([\text{"b"}] \mathbin{+\!\!+} [\,]) = [\text{"a"}, \text{"b"}]$.

**Example (Permutations as an equivalence functor).** `Equiv.Perm` is an `EquivFunctor` with $\mathrm{map}\,e\,p = e \circ p \circ e^{-1}$, the conjugation. Let $e \colon \{0, 1, 2\} \simeq \{a, b, c\}$ send $0, 1, 2$ to $a, b, c$, and let $p$ swap $0$ and $1$. Then $\mathrm{map}\,e\,p$ sends $a \mapsto e(p(0)) = b$, $b \mapsto a$ and $c \mapsto c$: it swaps $a$ and $b$. `Equiv.Perm` is not a functor, since a function $\alpha \to \beta$ that is not bijective does not carry permutations of $\alpha$ to permutations of $\beta$.

### The library around it

::: mathlib
`map_seq` · `Mathlib.Control.Basic`

The file collects consequences of the laws. `map_seq` and `seq_map_assoc` move maps through `<*>`, `seq_bind_eq` moves a map through `>>=`, and `fish_pure`, `fish_pipe` and `fish_assoc` are the Kleisli laws. `joinM_pure`, `joinM_map_pure`, `joinM_map_map` and `joinM_map_joinM` are the join laws. `zipWithM`, `List.mapAccumLM` and `List.mapAccumRM` are monadic list combinators. `Sum.bind` with `Sum.instMonad_mathlib` and `Sum.instLawfulMonad_mathlib` is the sum monad. The class `CommApplicative` and `CommApplicative.commutative_map` state commutativity for any binary function.

<?decl map_seq?>
:::

::: mathlib
`Functor.Comp` · `Mathlib.Control.Functor`

`Functor.Comp F G α` is `F (G α)`, with `Comp.mk` and `Comp.run`. The functor instance and `Functor.Comp.lawfulFunctor` are in this file, and the applicative instance with `Functor.Comp.instLawfulApplicativeComp`, `Functor.Comp.seq_assoc` and the commutative instance are in `Mathlib.Control.Applicative`. The same file has `Functor.Const α`, whose map ignores the function, and `Functor.AddConst`. These become applicative when $\alpha$ is a monoid, and the next section folds with them. `Functor.Liftp p x` says that $x$ is the image of a value in `F (Subtype p)`, and `Functor.supp x` is the set of points of every such predicate. `Functor.ext` and `Applicative.ext` show that two lawful instances with the same operations are equal.

<?decl Functor.Comp?>
:::

::: mathlib
`ContT` · `Mathlib.Control.Monad.Cont`

`ContT r m α := (α → m r) → m r`, with `ContT.run`, the monad instance, `ContT.run_pure`, `ContT.run_bind` and `ContT.run_callCC`. The class `MonadCont` gives `callCC` with labels `MonadCont.Label` and `goto`. `LawfulMonadCont` adds `callCC_bind_right`, `callCC_bind_left` (a jump to a label at once returns the value) and `callCC_dummy` (an unused label changes nothing).

<?decl ContT?>
:::

::: mathlib
`WriterT` · `Mathlib.Control.Monad.Writer`

`WriterT ω M α := M (α × ω)`, with `WriterT.mk` and `WriterT.run`. `WriterT.monad empty append` builds the monad from any neutral element and operation, and `run_pure`, `run_bind` and `run_tell` compute with it. There are two instances, for `[EmptyCollection ω] [Append ω]` and for `[Monoid ω]`, and the lawful instance needs `[Monoid ω] [LawfulMonad M]`. The class `MonadWriter` has `tell`, `listen` and `pass`.

<?decl WriterT?>
:::

::: mathlib
`ULiftable` · `Mathlib.Control.ULiftable`

`ULiftable f g` transports equivalences: `congr : α ≃ β → f α ≃ g β`. `ULiftable.up` and `ULiftable.down` move a value to and from `g (ULift α)`, with `up_down` and `down_up`. The monad instances for `ULift` and `PLift`, with `ULift.bind`, are in `Mathlib.Control.ULift`.

<?decl ULiftable?>
:::

::: mathlib
`EquivFunctor.mapEquiv` · `Mathlib.Control.EquivFunctor`

The class `EquivFunctor` has `map`, `map_refl'` and `map_trans'`, and `mapEquiv f e : f α ≃ f β` packs `map e` with `map e.symm`. `mapEquiv_trans` states that it respects composition. `EquivFunctor.ofLawfulFunctor` makes each lawful functor an equivalence functor, and `mapEquiv.injective` shows that $e \mapsto \mathrm{mapEquiv}\,f\,e$ is injective when `pure` is injective. `Mathlib.Control.EquivFunctor.Instances` has `EquivFunctorPerm`, `EquivFunctorFinset` (map along `e.toEmbedding`), `EquivFunctorUnique` and `EquivFunctorFintype`.

<?decl EquivFunctor.mapEquiv?>
:::

::: mathlib
`Bifunctor` · `Mathlib.Control.Bifunctor`

`Bifunctor F` has `bimap`, and `LawfulBifunctor` has `id_bimap` and `bimap_bimap`. `Bifunctor.fst` and `Bifunctor.snd` are the one-sided maps, with `id_fst`, `comp_fst`, `fst_snd`, `snd_fst` and `comp_snd`. Instances: `Prod.bifunctor` (`Prod.map`), `Sum.bifunctor` (`Sum.map`), `Bifunctor.const`, `Bifunctor.flip`, and the compositions with `Function.bicompl` and `Function.bicompr`. `Bifunctor.functor` makes `F α` a functor by `snd`.

<?decl Bifunctor?>
:::

Common errors of a learner: The first error is to expect a lemma such as `map_seq` to apply to a monad that has no `LawfulMonad` instance; the laws are separate classes, and the writer monad over `List String` has no lawful instance. The second error is to state a theorem with `>>=` in one place and `<$>` in another, and then fail to close the goal; `map_eq_bind_pure_comp` and `seq_bind_eq` convert between the forms. The third error is to read `callCC f` as "run $f$ and then continue"; after `goto` the rest of the block is never run. The fourth error is to look for a `Functor` instance of `Equiv.Perm`; there is only an `EquivFunctor` instance.

### Exercises

1. (A) Compute $[1, 2, 3] \mathbin{>>=} (\lambda n.\, \mathrm{List.replicate}\,n\,n)$ in the list monad. Hint: the answer has six elements.
2. (A) Show that $f \mathbin{<\$>} \mathrm{inl}\,u = \mathrm{inl}\,u$ in `Sum e` and that $\mathrm{joinM}(\mathrm{inr}(\mathrm{inl}\,u)) = \mathrm{inl}\,u$. Hint: unfold `Sum.bind`.
3. (A) Compute $\mathrm{snd}\,(\cdot + 1)\,(\mathrm{fst}\,(\cdot \cdot 2)\,(\mathrm{inl}\,3))$ for the bifunctor `Sum`. Hint: `Sum.map` acts on one side only.
4. (B) Prove $\mathrm{joinM}(g \mathbin{<\$>} a) = a \mathbin{>>=} g$ for a lawful monad, and deduce $x \mathbin{>>=} f = \mathrm{joinM}(f \mathbin{<\$>} x)$. Hint: use `seq_bind_eq` with the identity.
5. (B) Show that `Option` satisfies the law of `CommApplicative`. Hint: there are four cases, `some` or `none` for each argument.
6. (B) Run `callCC (fun k => pure 7)` in `Cont Nat` with continuation $\mathrm{id}$, and compare with the law `callCC_dummy`. Hint: the label is never used.
7. (C) Show that $\mathrm{pure} \colon \alpha \to \mathrm{List}\,\alpha$ is injective, and deduce that $e \mapsto \mathrm{mapEquiv}\,\mathrm{List}\,e$ is injective. Then give a type constructor $f$ with a lawful functor instance for which this map is not injective. Hint: try $f\,\alpha = \mathrm{Unit}$.

### Notes and history

Moggi introduced monads as a model of computational effects in 1989 and 1991, and Wadler made them a tool of functional programming. McBride and Paterson introduced applicative functors in 2008, with the four laws used here.

The Mathlib files are by these authors, read from their headers: `Mathlib.Control.Basic` by Johannes Hölzl, `Mathlib.Control.Applicative`, `Mathlib.Control.Functor`, `Mathlib.Control.Monad.Basic`, `Mathlib.Control.Monad.Cont`, `Mathlib.Control.ULiftable` and `Mathlib.Control.Bifunctor` by Simon Hudon, `Mathlib.Control.Combinators` by Jeremy Avigad and Leonardo de Moura, `Mathlib.Control.Lawful` by Sebastian Ullrich, `Mathlib.Control.Monad.Writer` by Simon Hudon, Edward Ayers and Eric Wieser, `Mathlib.Control.ULift` by Kim Morrison and Jannis Limperg, and `Mathlib.Control.EquivFunctor` and `Mathlib.Control.EquivFunctor.Instances` by Kim Morrison.

### Reference

<?reference?>
