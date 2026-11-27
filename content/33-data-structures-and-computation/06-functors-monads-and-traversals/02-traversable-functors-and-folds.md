---
title: Traversable functors and folds
kind: theory
modules:
  - Mathlib.Control.Traversable.Basic
  - Mathlib.Control.Traversable.Equiv
  - Mathlib.Control.Traversable.Instances
  - Mathlib.Control.Traversable.Lemmas
  - Mathlib.Control.Bitraversable.Basic
  - Mathlib.Control.Bitraversable.Instances
  - Mathlib.Control.Bitraversable.Lemmas
  - Mathlib.Control.Fold
  - Mathlib.Data.DList.Instances
explains:
  E3: [Traversable, sequence, LawfulTraversable, ApplicativeTransformation, ApplicativeTransformation.preserves_map, Traversable.pure_traverse, Traversable.map_traverse, List.traverse_append, Sum.traverse, Equiv.traverse, Equiv.isLawfulTraversable, Bitraversable, LawfulBitraversable, Bitraversable.tfst, Traversable.foldMap, Traversable.mapFold, Traversable.foldMap_hom, Traversable.foldl, Traversable.foldr, Traversable.toList, Traversable.toList_spec, Traversable.foldl_toList, Batteries.DList.listEquivDList]
  E2: [List.mem_traverse, Traversable.traverse, LawfulTraversable.id_traverse, LawfulTraversable.comp_traverse, LawfulTraversable.traverse_eq_map_id, LawfulTraversable.naturality, Traversable.PureTransformation, Traversable.traverse_map, Traversable.map_eq_traverse_id, instLawfulTraversableOption, List.instLawfulTraversable, Sum.instLawfulTraversable, List.traverse_cons, Equiv.map, Equiv.traversable, bisequence, Prod.bitraverse, Sum.bitraverse, Bitraversable.tsnd, Bitraversable.tfst_eq_fst_id, Bitraversable.traversable, Monoid.Foldl, Monoid.Foldr, Traversable.foldMap_hom_free, Traversable.foldr_toList, Traversable.toList_map, Traversable.toList_eq_self, Traversable.length, Batteries.instLawfulTraversableDList]
  E1: auto
families: []
requires: [V01.C04, V03.C02, V05.C01, V05.C02, V33.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Traversable functors and folds

### Overview

A map applies a pure function to each element of a container. Often the function has an effect: it can fail, or it can return several answers. With `map`, a function `f : α → Option β` turns `List α` into `List (Option β)`, a list of separate results. The useful answer has type `Option (List β)`: `some` of the values when every call succeeds, and `none` otherwise. The operation `traverse` gives it. It applies the function to each element in order, combines the effects with the applicative structure, and rebuilds the container inside the effect.

This section defines the class `Traversable` and its laws, proves their main consequences, gives the instances for `Option`, `List` and `Sum`, moves instances along equivalences (which gives difference lists), and treats `Bitraversable`. The last part derives the folds from `traverse`: with the constant applicative functor of a monoid, a traversal computes a product, and the choice of the monoid gives `foldl`, `foldr`, `toList` and `length`.

### Definitions

**Definition (Traversable functor).** A traversable functor is a functor `t : Type u → Type u` with an operation $$\mathrm{traverse} \colon (\alpha \to m\,\beta) \to t\,\alpha \to m\,(t\,\beta)$$ for every applicative functor `m : Type u → Type u`. The derived operation `sequence : t (m α) → m (t α)` is `traverse id`: it pulls the effects out of the container.

For lists, `traverse f [] = pure []` and `traverse f (a :: l) = List.cons <$> f a <*> traverse f l` (`List.traverse_nil` and `List.traverse_cons`). For options, `traverse f none = pure none` and `traverse f (some a) = some <$> f a`. For `Sum σ`, the traversal acts on the right summand only: `Sum.traverse f (inl x) = pure (inl x)` and `Sum.traverse f (inr a) = inr <$> f a`.

**Definition (Applicative transformation).** For applicative functors $F$ and $G$, an applicative transformation $\eta \colon F \Rightarrow G$ is a family of functions $\eta_\alpha \colon F\,\alpha \to G\,\alpha$ with $\eta(\mathrm{pure}\,x) = \mathrm{pure}\,x$ and $\eta(u \mathbin{<*>} v) = \eta\,u \mathbin{<*>} \eta\,v$. The structure is `ApplicativeTransformation F G`. There is an identity `idTransformation` and a composite `ApplicativeTransformation.comp`. For a lawful applicative functor $F$, `Traversable.PureTransformation F` is the transformation $\mathrm{Id} \Rightarrow F$ given by `pure`.

**Definition (Lawful traversable functor).** A traversable functor is lawful (`LawfulTraversable t`) if it is a lawful functor and these four laws hold for all lawful applicative functors $F$ and $G$:

1. identity: `traverse (pure : α → Id α) x = pure x`;
2. composition: `traverse (Comp.mk ∘ map f ∘ g) x = Comp.mk (map (traverse f) (traverse g x))` for $g \colon \alpha \to G\,\beta$ and $f \colon \beta \to F\,\gamma$;
3. agreement with map: `traverse ((pure : β → Id β) ∘ f) x = pure (f <$> x)`;
4. naturality: `η (traverse f x) = traverse (η ∘ f) x` for each applicative transformation $\eta \colon F \Rightarrow G$.

The composition law says that two traversals in a row, first with the effects of $G$ and then with those of $F$, are one traversal with the composite effect `Functor.Comp G F`. Naturality says that a traversal only combines the effects with `pure` and `<*>`.

**Definition (Equivalence transport).** Let `t` be traversable and let `eqv : ∀ α, t α ≃ t' α` be a family of equivalences. Then `Equiv.map eqv f x = eqv β (map f ((eqv α).symm x))` and $$\mathrm{Equiv.traverse}\ \mathrm{eqv}\ f\ x = \mathrm{eqv}\,\beta \mathbin{<\$>} \mathrm{traverse}\,f\,((\mathrm{eqv}\,\alpha)^{-1}\,x).$$ They form the functor `Equiv.functor eqv` and the traversable functor `Equiv.traversable eqv` on `t'`.

**Definition (Bitraversable functor).** A bitraversable functor is a bifunctor `t : Type u → Type u → Type u` with $\mathrm{bitraverse} \colon (\alpha \to m\,\alpha') \to (\beta \to m\,\beta') \to t\,\alpha\,\beta \to m\,(t\,\alpha'\,\beta')$. For pairs, `Prod.bitraverse f f' (x, y) = Prod.mk <$> f x <*> f' y`. `Sum.bitraverse` is similar. The one-sided traversals are `tfst f = bitraverse f pure` and `tsnd f = bitraverse pure f`, and `bisequence = bitraverse id id`. The class `LawfulBitraversable` states the same four laws as `LawfulTraversable`, with two functions in place of one.

**Definition (Constant applicative functor of a monoid).** For a monoid $(\omega, \cdot, 1)$, the functor `Functor.Const ω` sends every type to $\omega$, and its map does nothing. It is applicative with $\mathrm{pure}\,\_ = 1$ and $u \mathbin{<*>} v = u \cdot v$, and it is lawful because $1$ is neutral and the product is associative. A traversal with it only multiplies the values in order: $$\mathrm{foldMap}\,f\,x = \mathrm{traverse}\,(\mathrm{Const.mk'} \circ f)\,x \in \omega.$$

**Definition (Folds).** Let `Monoid.Foldr α` be the monoid of functions $\alpha \to \alpha$ with $g \cdot h = g \circ h$, and let `Monoid.Foldl α` be the same set with the opposite product, $g \cdot h = h \circ g$. Then

- `foldr f x xs = (foldMap (Foldr.mk ∘ f) xs).get x`, for $f \colon \alpha \to \beta \to \beta$;
- `foldl f x xs = (foldMap (Foldl.mk ∘ flip f) xs).get x`, for $f \colon \alpha \to \beta \to \alpha$;
- `toList = List.reverse ∘ foldl (flip List.cons) []`;
- `length xs` counts the elements with `foldl (fun n _ => n + 1) 0`.

**Definition (Difference list).** A difference list `Batteries.DList α` is a function `apply : List α → List α` with the invariant `apply l = apply [] ++ l`. The list $l$ becomes the function $(l \mathbin{+\!\!+} \cdot)$ by `DList.ofList`, and `DList.toList d` is `d.apply []`. Append is composition, in constant time. By the invariant, `ofList` and `toList` are inverse, and `DList.listEquivDList α : List α ≃ DList α` is this equivalence.

### Theorems and proofs

**Lemma (Transformations preserve map).** If $F$ and $G$ are lawful and $\eta \colon F \Rightarrow G$ is an applicative transformation, then $\eta(f \mathbin{<\$>} y) = f \mathbin{<\$>} \eta\,y$.

*Proof.* In a lawful applicative functor, $f \mathbin{<\$>} y = \mathrm{pure}\,f \mathbin{<*>} y$. So $$\eta(f \mathbin{<\$>} y) = \eta(\mathrm{pure}\,f \mathbin{<*>} y) = \eta(\mathrm{pure}\,f) \mathbin{<*>} \eta\,y = \mathrm{pure}\,f \mathbin{<*>} \eta\,y = f \mathbin{<\$>} \eta\,y.$$ The second step is the preservation of `<*>`, the third is the preservation of `pure`, and the last is the law of $G$. $\square$

This is `ApplicativeTransformation.preserves_map`.

**Proposition (Traversal with pure).** In a lawful traversable functor and a lawful applicative functor $F$, `traverse pure x = (pure x : F (t α))`.

*Proof.* Let $\eta$ be `PureTransformation F`, so $\eta_\alpha = \mathrm{pure}_F$ on `Id α`. Apply naturality to the function $\mathrm{pure}_{\mathrm{Id}} \colon \alpha \to \mathrm{Id}\,\alpha$: $$\eta(\mathrm{traverse}\,\mathrm{pure}_{\mathrm{Id}}\,x) = \mathrm{traverse}\,(\eta \circ \mathrm{pure}_{\mathrm{Id}})\,x.$$ In `Id`, `pure` is the identity, so $\eta \circ \mathrm{pure}_{\mathrm{Id}} = \mathrm{pure}_F$ and the right side is `traverse pure x` in $F$. On the left side, the identity law gives $\mathrm{traverse}\,\mathrm{pure}_{\mathrm{Id}}\,x = x$, so the left side is $\mathrm{pure}_F\,x$. $\square$

This is `Traversable.pure_traverse`.

**Proposition (Map after traverse).** In a lawful traversable functor, $\mathrm{map}\,f \mathbin{<\$>} \mathrm{traverse}\,g\,x = \mathrm{traverse}\,(\mathrm{map}\,f \circ g)\,x$ for $g \colon \alpha \to F\,\beta$ and $f \colon \beta \to \gamma$.

*Proof.* By the third law, `map f = Id.run ∘ traverse (pure ∘ f)` (`Traversable.map_eq_traverse_id`). Apply the composition law with $F$ as the first effect and `Id` as the second: $$\mathrm{traverse}\,(\mathrm{Comp.mk} \circ \mathrm{map}\,(\mathrm{pure} \circ f) \circ g)\,x = \mathrm{Comp.mk}\,(\mathrm{map}\,(\mathrm{traverse}\,(\mathrm{pure} \circ f))\,(\mathrm{traverse}\,g\,x)).$$ Up to the identity wrapper, `Comp F Id` is $F$ (`Comp.applicative_comp_id`). Read in $F$, the left side is `traverse (map f ∘ g) x` and the right side is `map f <$> traverse g x`. $\square$

The companion `Traversable.traverse_map` states $\mathrm{traverse}\,f\,(g \mathbin{<\$>} x) = \mathrm{traverse}\,(f \circ g)\,x$, with the same proof and `Id` as the first effect.

**Proposition (Traversal of an append).** For a lawful applicative functor $F$ and lists $a$ and $b$, $$\mathrm{traverse}\,f\,(a \mathbin{+\!\!+} b) = (\cdot \mathbin{+\!\!+} \cdot) \mathbin{<\$>} \mathrm{traverse}\,f\,a \mathbin{<*>} \mathrm{traverse}\,f\,b.$$

*Proof.* Induction on $a$. Write $T\,l$ for `traverse f l` and $h$ for $(\cdot \mathbin{+\!\!+} \cdot)$. For $a = []$, the right side is $h \mathbin{<\$>} \mathrm{pure}\,[] \mathbin{<*>} T\,b = \mathrm{pure}\,(h\,[]) \mathbin{<*>} T\,b = ([] \mathbin{+\!\!+} \cdot) \mathbin{<\$>} T\,b = T\,b$, which is the left side. For $a = x :: a'$, the left side is $\mathrm{cons} \mathbin{<\$>} f\,x \mathbin{<*>} T(a' \mathbin{+\!\!+} b)$, and by the induction hypothesis it is $$\mathrm{cons} \mathbin{<\$>} f\,x \mathbin{<*>} (h \mathbin{<\$>} T\,a' \mathbin{<*>} T\,b).$$ The associativity law of `<*>` and the lemma `seq_map_assoc` of the previous section turn this into $k \mathbin{<\$>} f\,x \mathbin{<*>} T\,a' \mathbin{<*>} T\,b$ with $k\,y\,l\,m = y :: (l \mathbin{+\!\!+} m)$. The right side is $h \mathbin{<\$>} (\mathrm{cons} \mathbin{<\$>} f\,x \mathbin{<*>} T\,a') \mathbin{<*>} T\,b$. The lemma `map_seq` and the composition law of the functor turn it into $k' \mathbin{<\$>} f\,x \mathbin{<*>} T\,a' \mathbin{<*>} T\,b$ with $k'\,y\,l\,m = (y :: l) \mathbin{+\!\!+} m$. Since $(y :: l) \mathbin{+\!\!+} m = y :: (l \mathbin{+\!\!+} m)$, the functions $k$ and $k'$ are equal. $\square$

In the set applicative, the same induction proves `List.mem_traverse`: a list $n$ is in `traverse f l` if and only if `Forall₂ (fun b a => b ∈ f a) n l`, so the traversal lists all the ways to choose one value $n_i \in f(l_i)$ for each position.

**Theorem (Transport of lawful instances).** If `t` is a lawful traversable functor and `eqv : ∀ α, t α ≃ t' α`, then `t'` with `Equiv.traversable eqv` is a lawful traversable functor.

*Proof.* Write $e$ for `eqv` and $e^{-1}$ for its inverse, and let $y = e^{-1}\,x$. Identity: $\mathrm{Equiv.traverse}\,e\,\mathrm{pure}\,x = e \mathbin{<\$>} \mathrm{traverse}\,\mathrm{pure}\,y = e \mathbin{<\$>} \mathrm{pure}\,y = \mathrm{pure}(e\,y) = \mathrm{pure}\,x$. Agreement with map: $e \mathbin{<\$>} \mathrm{traverse}\,(\mathrm{pure} \circ f)\,y = e \mathbin{<\$>} \mathrm{pure}(f \mathbin{<\$>} y) = \mathrm{pure}(e(f \mathbin{<\$>} e^{-1}\,x))$, which is $\mathrm{pure}(\mathrm{Equiv.map}\,e\,f\,x)$. Naturality: by the lemma on maps, $\eta(e \mathbin{<\$>} \mathrm{traverse}\,f\,y) = e \mathbin{<\$>} \eta(\mathrm{traverse}\,f\,y) = e \mathbin{<\$>} \mathrm{traverse}\,(\eta \circ f)\,y$. Composition: both sides reduce to $\mathrm{Comp.mk}((\mathrm{map}\,e \circ \mathrm{traverse}\,f) \mathbin{<\$>} \mathrm{traverse}\,g\,y)$, the right side because $\mathrm{Equiv.traverse}\,e\,f\,(e\,z) = e \mathbin{<\$>} \mathrm{traverse}\,f\,(e^{-1}(e\,z)) = e \mathbin{<\$>} \mathrm{traverse}\,f\,z$ for each $z$. The functor laws for `Equiv.map` follow from those of `t` in the same way. $\square$

This is `Equiv.isLawfulTraversable`. The instances for `DList` are `Equiv.traversable` and `Equiv.isLawfulTraversable` applied to `listEquivDList`.

**Theorem (Folds are monoid homomorphisms).** Let `t` be lawful, let $\phi \colon \omega \to \omega'$ be a monoid homomorphism and let $g \colon \gamma \to \omega$. Then $\phi(\mathrm{foldMap}\,g\,x) = \mathrm{foldMap}\,(\phi \circ g)\,x$.

*Proof.* Define $\eta \colon \mathrm{Const}\,\omega \Rightarrow \mathrm{Const}\,\omega'$ by $\eta = \phi$ on each type. It preserves `pure` since $\phi(1) = 1$, and it preserves `<*>` since $\phi(u \cdot v) = \phi(u) \cdot \phi(v)$. So $\eta$ is an applicative transformation (`Traversable.mapFold`). Naturality gives $$\phi(\mathrm{traverse}\,(\mathrm{Const.mk'} \circ g)\,x) = \mathrm{traverse}\,(\eta \circ \mathrm{Const.mk'} \circ g)\,x = \mathrm{traverse}\,(\mathrm{Const.mk'} \circ \phi \circ g)\,x,$$ which is the claim. $\square$

**Theorem (Folds through the list of elements).** For a lawful traversable functor, `toList xs = FreeMonoid.toList (foldMap FreeMonoid.of xs)` and `foldl f x xs = List.foldl f x (toList xs)`. The same holds for `foldr`.

*Proof.* Let $L$ be the list `FreeMonoid.toList (foldMap FreeMonoid.of xs)`. The map $\Phi$ that sends a word $w$ of the free monoid to the function $a \mapsto \mathrm{List.foldl}\,f\,a\,w$ in `Foldl β` is a monoid homomorphism (`Monoid.Foldl.ofFreeMonoid f`): the empty word gives the identity, and `List.foldl f a (w ++ w') = List.foldl f (List.foldl f a w) w'` is the product in the opposite order. On a single letter, $\Phi(\mathrm{of}\,b)$ is $a \mapsto f\,a\,b$, which is `Foldl.mk (flip f b)`. By the previous theorem, $$\mathrm{foldMap}\,(\mathrm{Foldl.mk} \circ \mathrm{flip}\,f)\,xs = \mathrm{foldMap}\,(\Phi \circ \mathrm{of})\,xs = \Phi(\mathrm{foldMap}\,\mathrm{of}\,xs).$$ Evaluate at $x$: `foldl f x xs = List.foldl f x L`. Take $f = \mathrm{flip}\,\mathrm{cons}$ and $x = []$: $\mathrm{List.foldl}\,(\mathrm{flip}\,\mathrm{cons})\,[]\,L$ is the reverse of $L$, by induction on $L$. So $\mathrm{toList}\,xs = \mathrm{reverse}(\mathrm{reverse}\,L) = L$, the first claim. Then `foldl f x xs = List.foldl f x L = List.foldl f x (toList xs)`. For `foldr`, the homomorphism is `Foldr.ofFreeMonoid f` with `List.foldr_append`. $\square$

These are `Traversable.toList_spec`, `Traversable.foldl_toList` and `Traversable.foldr_toList`. They reduce questions on folds to questions on lists.

### Examples

**Example (Traverse with Option).** Let `half n = if n % 2 = 0 then some (n / 2) else none`. Then, from the right end:

- `traverse half [6] = cons <$> some 3 <*> some [] = some [3]`;
- `traverse half [4, 6] = cons <$> some 2 <*> some [3] = some [2, 3]`;
- `traverse half [2, 4, 6] = cons <$> some 1 <*> some [2, 3] = some [1, 2, 3]`.

For `[2, 3, 6]`, the call `half 3` is `none`, so `cons <$> none <*> some [3]` is `none`, and the last step `cons <$> some 1 <*> none` is `none`.

```lean
example : traverse (fun n : ℕ => if n % 2 = 0 then some (n / 2) else none) [2, 4, 6]
    = some [1, 2, 3] := rfl
```

**Example (Sequence in the list monad).** With the list applicative, `sequence [[1, 2], [3]]` lists the choices. First `sequence [[3]] = cons <$> [3] <*> [[]] = [[3]]`. Then `sequence [[1, 2], [3]] = cons <$> [1, 2] <*> [[3]] = [[1, 3], [2, 3]]`.

**Example (Folds of [3, 1, 2]).** In the multiplicative monoid ℕ, `foldMap id [3, 1, 2] = 3 · (1 · (2 · 1)) = 6`. Over ℤ, put $g_y\,a = a - y$. Then `foldl (· - ·) 10 [3, 1, 2]` multiplies $g_3, g_1, g_2$ in `Foldl ℤ`, which is the function $g_2 \circ g_1 \circ g_3$, and at $10$ it gives $((10 - 3) - 1) - 2 = 4$. In `Foldr ℤ`, the product of $h_3, h_1, h_2$ with $h_a\,b = a - b$ is $h_3 \circ h_1 \circ h_2$, so `foldr (· - ·) 10 [3, 1, 2]` is $3 - (1 - (2 - 10)) = 3 - 9 = -6$. For other containers, `toList (some 5) = reverse [5] = [5]`, `length (none : Option ℕ) = 0`, and `toList (inl 3 : ℕ ⊕ ℕ) = []`.

**Example (Bitraverse of a pair).** `bitraverse half half (4, 6) = Prod.mk <$> some 2 <*> some 3 = some (2, 3)`. Also `tfst half (3, 6) = Prod.mk <$> none <*> pure 6 = none` and `tsnd half (3, 6) = some (3, 3)`.

**Example (Difference lists).** `DList.ofList [1, 2]` is the function $l \mapsto [1, 2] \mathbin{+\!\!+} l$, and its append with `DList.ofList [3]` is the composite $l \mapsto [1, 2] \mathbin{+\!\!+} ([3] \mathbin{+\!\!+} l)$, with `toList` equal to $[1, 2, 3]$. The transported traversal gives `traverse half (DList.ofList [2, 4]) = DList.ofList <$> traverse half [2, 4] = some (DList.ofList [1, 2])`.

### The library around it

::: mathlib
`Traversable` · `Mathlib.Control.Traversable.Basic`

The class `Traversable t` extends `Functor t` with `traverse`. `Mathlib.Control.Traversable.Lemmas` has `PureTransformation`, `map_eq_traverse_id`, `traverse_map`, `pure_traverse`, `id_sequence` and `comp_sequence`. `LawfulTraversable t` extends `LawfulFunctor t` with `id_traverse`, `comp_traverse`, `traverse_eq_map_id` and `naturality`. `ApplicativeTransformation F G` has `app`, `preserves_pure'` and `preserves_seq'`. The file gives the instances for `Id`, `Option`, `List` and `Sum σ` (with `Sum.traverse`), and the lawful instance for `Id`.

<?decl Traversable?>
:::

::: mathlib
`List.mem_traverse` · `Mathlib.Control.Traversable.Instances`

The lawful instances `instLawfulTraversableOption`, `List.instLawfulTraversable` and `Sum.instLawfulTraversable` are proved by cases or induction. For lists, `traverse_nil`, `traverse_cons` and `traverse_append` compute, and `mem_traverse` describes traversals in `Set` with `List.Forall₂`.

<?decl List.mem_traverse?>
:::

::: mathlib
`Equiv.isLawfulTraversable` · `Mathlib.Control.Traversable.Equiv`

`Equiv.map`, `Equiv.functor`, `Equiv.traverse` and `Equiv.traversable` move the structure along `eqv : ∀ α, t α ≃ t' α`. `Equiv.lawfulFunctor` and `Equiv.isLawfulTraversable` move the laws. `Mathlib.Data.DList.Instances` uses this with `Batteries.DList.listEquivDList`.

<?decl Equiv.isLawfulTraversable?>
:::

::: mathlib
`LawfulBitraversable` · `Mathlib.Control.Bitraversable.Basic`

`Bitraversable t` extends `Bifunctor t` with `bitraverse`, and `bisequence` is `bitraverse id id`. `LawfulBitraversable` has `id_bitraverse`, `comp_bitraverse`, `bitraverse_eq_bimap_id` and `binaturality`. `Mathlib.Control.Bitraversable.Lemmas` defines `tfst` and `tsnd` with `comp_tfst`, `comp_tsnd` and `tfst_eq_fst_id`. `Mathlib.Control.Bitraversable.Instances` covers `Prod`, `Sum`, `Const`, `flip`, `Function.bicompl` and `Function.bicompr`, and `Bitraversable.traversable` makes each `t α` traversable by `tsnd`.

<?decl LawfulBitraversable?>
:::

::: mathlib
`Traversable.foldMap_hom` · `Mathlib.Control.Fold`

`foldMap`, `foldl`, `foldr`, `toList`, `length`, `foldlM` and `foldrM` are defined from `traverse` with the monoids `Monoid.Foldl`, `Monoid.Foldr`, `Monoid.foldlM` and `Monoid.foldrM`, and `mapFold` turns a monoid homomorphism into an applicative transformation. The main lemmas are `foldMap_hom`, `foldMap_hom_free`, `toList_spec`, `foldl_toList`, `foldr_toList`, `toList_map` and `toList_eq_self`.

<?decl Traversable.foldMap_hom?>
:::

Common errors of a learner: The first error is to use `map` with an effectful function and get a container of effects, such as `List (Option β)`, where `traverse` gives the effect of a container. The second error is to apply a lemma such as `foldl_toList` without a `LawfulTraversable` instance; the folds are defined for every traversable functor, but the lemmas need the laws. The third error is to read `toList` as `foldMap FreeMonoid.of`; that is the theorem `toList_spec`, and the definition uses `foldl` and `reverse` so that it runs in linear time.

### Exercises

1. (A) Compute `traverse half [8, 4]` and `traverse half [8, 5]`, and compute `sequence [[1, 2], [3, 4]]` in the list applicative. Hint: the last answer has four lists, in the order of a nested loop.
2. (A) Over ℤ, compute `foldr (· - ·) 0 [5, 2]`, `foldl (· - ·) 0 [5, 2]` and `length (inr 7 : ℕ ⊕ ℕ)` from the definitions of this section. Hint: `length` is a `foldl`.
3. (B) Prove `traverse f (l ++ [a]) = (fun l' b => l' ++ [b]) <$> traverse f l <*> f a` for a lawful applicative functor. Hint: use `List.traverse_append` and compute `traverse f [a]`.
4. (B) Prove that `sequence l = some l'` in `Option` if and only if `l = l'.map some`. Hint: induction on `l` and the case split on the head.
5. (B) Let `φ : FreeMonoid α →* Multiplicative ℕ` send a word to `Multiplicative.ofAdd` of its length. Use `foldMap_hom_free` and `toList_spec` to prove `foldMap (fun _ => Multiplicative.ofAdd 1) xs = Multiplicative.ofAdd (toList xs).length` for a lawful traversable functor. Hint: `φ ∘ FreeMonoid.of` is the constant function with value `ofAdd 1`.
6. (B) Prove the identity law of `LawfulBitraversable` for `Prod`: `bitraverse pure pure (x, y) = pure (x, y)` in `Id`. Hint: in `Id`, `<$>` and `<*>` are function application.
7. (C) Define `traverse' f l = List.reverse <$> traverse f l.reverse` on lists. Show that it satisfies the four laws of `LawfulTraversable` with the usual `map`, and that its `toList` reverses the list. Conclude that the laws do not fix the order in which the effects run. Hint: for the composition law, use `List.reverse_reverse` and the composition law of the functor.

### Notes and history

McBride and Paterson introduced applicative functors and the traversal operation in 2008. The header of `Mathlib.Control.Traversable.Basic` takes the laws from the Haskell library and cites McBride and Paterson, Gibbons and Oliveira, and Jaskelioff and Rypacek.

The Mathlib files are by these authors, read from their headers: `Mathlib.Control.Traversable.Basic`, `Mathlib.Control.Traversable.Equiv`, `Mathlib.Control.Traversable.Instances`, `Mathlib.Control.Traversable.Lemmas`, `Mathlib.Control.Bitraversable.Basic`, `Mathlib.Control.Bitraversable.Instances`, `Mathlib.Control.Bitraversable.Lemmas` and `Mathlib.Data.DList.Instances` by Simon Hudon, and `Mathlib.Control.Fold` by Simon Hudon and Sean Leather.

### Reference

<?reference?>
