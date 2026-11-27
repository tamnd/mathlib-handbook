---
title: Randomness and property testing
kind: theory
modules:
  - Mathlib.Control.Random
  - Mathlib.Testing.Plausible.Functions
  - Mathlib.Testing.Plausible.Sampleable
  - Mathlib.Testing.Plausible.Testable
explains:
  E3: [Random, BoundedRandom, RandGT, Random.randFin, Random.instBoundedRandomNat, Plausible.InjectiveFunction, Plausible.InjectiveFunction.applyId_injective, Plausible.InjectiveFunction.injective, Plausible.InjectiveFunction.shrink, Plausible.TotalFunction.applyFinsupp, Plausible.Rat.shrinkable]
  E2: [Rand, RandG, RandT, Rand.next, Rand.split, Rand.range, Random.rand, Random.randBound, Random.randBool, Random.instBoundedRandomInt, Random.instBoundedRandomFin, Random.instFinOfNeZeroNat, IO.runRand, IO.runRandWith, BoundedRandom.randomR, Plausible.InjectiveFunction.apply, Plausible.InjectiveFunction.List.applyId, Plausible.InjectiveFunction.List.applyId_cons, Plausible.InjectiveFunction.List.applyId_zip_eq, Plausible.InjectiveFunction.List.applyId_eq_self, Plausible.InjectiveFunction.applyId_mem_iff, Plausible.InjectiveFunction.mk, Plausible.InjectiveFunction.shrinkPerm, Plausible.InjectiveFunction.Perm.slice, Plausible.InjectiveFunction.sliceSizes, Plausible.InjectiveFunction.PiInjective.sampleableExt, Plausible.InjectiveFunction.instArbitraryInt, Plausible.TotalFunction.zeroDefault, Plausible.TotalFunction.zeroDefaultSupp, Plausible.TotalFunction.Finsupp.sampleableExt, Plausible.TotalFunction.DFinsupp.sampleableExt, Plausible.Injective.testable, Plausible.Monotone.testable, Plausible.Antitone.testable, Plausible.PNat.shrinkable, Plausible.PNat.Arbitrary, Plausible.Rat.Arbitrary, Plausible.Rat.sampleableExt, Plausible.Testable.factTestable]
  E1: auto
families: []
requires: [V01.C01, V03.C07, V33.C02, V33.C03, V33.C06]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Randomness and property testing

### Overview

Before a programmer proves a statement, the programmer often tests it: draw many random inputs, evaluate the statement on each, and report an input on which it fails. This is property based testing, and in Lean it is the `plausible` tactic of the Plausible library. This section first explains how a pure functional language produces random values at all: a random value is a function of the state of a generator, and the state passes from one draw to the next through the state monad of Chapter 6. It then proves that the bounded generators respect their bounds, builds random injective functions from random permutations, and builds random finitely supported functions from association lists. It ends with the limits of testing. A counterexample that a test reports is a real counterexample, but a test that finds none proves nothing, and the section gives a false statement about `UInt8` that the default test never refutes.

### Definitions

**Definition (Random computation).** Let $g$ be the type of the states of a generator, with an instance `RandomGen g`: a function `next : g → ℕ × g`, a function `split : g → g × g` and a range of values. A random computation with values in $\alpha$ in a monad $m$ is an element of `RandGT g m α`, which is the state monad `StateT (ULift g) m α`. Up to the universe lift, it is a function $g \to m(\alpha \times g)$: it reads the state, returns a value and a new state. `RandG g` is the case $m = $ `Id`, and `RandT` and `Rand` fix $g$ to the standard generator `StdGen`.

**Definition (Random type).** `Random m α` is a class with one field `random : RandGT g m α`, for each generator type $g$. So a type is random when it has a generator of values.

**Definition (Bounded random type).** For a preorder $\alpha$, `BoundedRandom m α` is a class with one field `randomR lo hi h`, where `h : lo ≤ hi`, of type `RandGT g m {a // lo ≤ a ∧ a ≤ hi}`. The value comes with a proof that it lies between the bounds.

**Definition (Generator steps).** `Rand.next` draws a natural number and stores the new state. `Rand.split` replaces the state by one half of a split and returns the other half, so that two computations can use independent streams. `IO.runRandWith seed c` runs `c` from the generator with the given seed and returns the value.

**Definition (Sampleable type and testable proposition).** In Plausible, `SampleableExt α` gives a proxy type with a generator (`Arbitrary`), a printer (`Repr`), a shrinker (`Shrinkable`) and a map `interp` from the proxy to $\alpha$. A shrinker maps a value $x$ to a list of smaller values. `Testable p` gives, for a proposition $p$, a random computation with a result of type `TestResult p`: either `success`, or `gaveUp n` when $n$ inputs did not satisfy a hypothesis, or `failure h xs n` with `h : ¬ p`, the printed counterexample `xs` and the number `n` of shrinking steps.

**Definition (Total function with a default).** In Plausible, a `TotalFunction α β` is `withDefault A y` with an association list $A$ of pairs $\langle a, b \rangle$ and a default $y$. It is the function $x \mapsto$ the value of the first pair with key $x$ in $A$, or $y$ if there is none.

**Definition (Injective function).** `Plausible.InjectiveFunction α` is `mapToSelf xs h₁ h₂` for an association list `xs`, a proof `h₁` that the list of keys is a permutation of the list of values, and a proof `h₂` that the values have no duplicates. Its function `apply` sends $x$ to the value of $x$ in `xs` if $x$ is a key, and to $x$ itself if not. For two lists, `List.applyId (xs.zip ys)` is the same function on the pairs of `xs.zip ys`.

### Theorems and proofs

**Proposition (Bounds of the generator of natural numbers).** Let $lo \le hi$ in $\mathbb{N}$. The instance `BoundedRandom m ℕ` draws $z$ in `Fin (hi - lo + 1)` and returns $lo + z$. Then $lo \le lo + z \le hi$.

*Proof.* The first inequality holds as $z \ge 0$. From $z < hi - lo + 1$ follows $z \le hi - lo$. As $lo \le hi$, the truncated difference satisfies $lo + (hi - lo) = hi$, so $lo + z \le lo + (hi - lo) = hi$. $\square$

The same argument for `ℤ` draws $z \in [0, |hi - lo|]$ in $\mathbb{N}$ and returns $z + lo$; as $hi - lo \ge 0$, $|hi - lo| = hi - lo$ and $lo \le z + lo \le hi$. For `Fin n`, the generator draws a natural number between the values of the bounds and keeps the proof that it is below $n$. The generator `Random.randFin` of `Fin n` needs `NeZero n`, since `Fin 0` is empty: it draws a natural number in $[0, n - 1]$ and reduces it modulo $n$.

**Theorem (Generated injective functions are injective).** Let `xs` have no duplicates and let `xs ~ ys`. Then $f = $ `List.applyId (xs.zip ys)` is injective.

*Proof.* First two facts. (a) If $x$ is the entry of `xs` at index $i$, then $f(x)$ is the entry of `ys` at index $i$ (`applyId_zip_eq`): the lookup returns the first pair with key $x$, and since `xs` has no duplicates this is the pair at index $i$. (b) $f(x) \in$ `ys` if and only if $x \in$ `xs` (`applyId_mem_iff`). If $x \in$ `xs`, then $f(x) \in$ `ys` by (a). If $x \notin$ `xs`, then $f(x) = x$ (`applyId_eq_self`), and $x \notin$ `ys`, as a permutation has the same members. Now let $f(x) = f(y)$. If $x, y \in$ `xs`, at indices $i$ and $j$, then (a) gives `ys[i] = ys[j]`. The list `ys` has no duplicates, as it is a permutation of `xs`, so $i = j$ and $x = y$. If $x \in$ `xs` and $y \notin$ `xs`, then $f(x) \in$ `ys` and $f(y) \notin$ `ys` by (b), which contradicts $f(x) = f(y)$; the case with $x$ and $y$ exchanged is the same. If $x, y \notin$ `xs`, then $x = f(x) = f(y) = y$. $\square$

**Corollary (Injective function data).** For each `InjectiveFunction α`, the function `apply` is injective (`InjectiveFunction.injective`).

*Proof.* Write the association list as the zip of its keys `xs₀` and its values `xs₁`. The values have no duplicates and are a permutation of the keys, so the keys have no duplicates, and `apply` is `List.applyId (xs₀.zip xs₁)`. Apply the theorem. $\square$

**Proposition (Shrinking keeps injectivity).** `InjectiveFunction.shrink` removes a block of consecutive keys and removes the same elements from the values. The result is again an injective function.

*Proof.* Let `xs ~ ys` with `ys` without duplicates, and let `xs'` be `xs` with a block removed. The new values are `ys' = ys.inter xs'`, the elements of `ys` that lie in `xs'`, in the order of `ys`. A permutation keeps the multiplicity of each element, and filtering both sides by the same predicate keeps it again, so `xs'` is a permutation of `ys'` (`List.Perm.dropSlice_inter`). A sublist of a list without duplicates has none. So `xs'` and `ys'` satisfy the hypotheses of the theorem. $\square$

**Proposition (Finitely supported functions from total functions).** Let $\beta$ have a zero and decidable equality. For `withDefault A y`, the function `applyFinsupp` replaces the default by $0$ and has as support the keys of $A$, without repetition, whose first value is nonzero. This set is exactly $\{a : \text{value at } a \ne 0\}$.

*Proof.* After the change of default, the value at $a$ is the first value of $a$ in $A$ if $a$ is a key, and $0$ if not. Removing the later pairs with a repeated key (`dedupKeys`) does not change the first value of any key. So $a$ is in the filtered list of keys if and only if $a$ is a key with nonzero first value, if and only if the value at $a$ is nonzero, as a non-key has value $0$. $\square$

**Proposition (Reported counterexamples are sound).** If the test of $\forall x, \beta(x)$ returns a failure, then $\neg \forall x, \beta(x)$ holds.

*Proof.* The test draws $x_0$ and tests $\beta(x_0)$. A failure of that test carries a proof $h$ of $\neg \beta(x_0)$, by the type of `failure`. From $H \colon \forall x, \beta(x)$ follows $\beta(x_0)$ and then a contradiction with $h$, so $\neg \forall x, \beta(x)$, and the test of the quantifier returns this proof. The other cases build the proof in the same way: for a decidable proposition $p$, a failure is the answer `false` of the decision procedure, which gives $\neg p$; for $p \to q$, a failure gives $p$ and $\neg q$, hence $\neg(p \to q)$. Shrinking replaces $x_0$ by a value with a new failure, and so a new proof. $\square$

This proof is about the terms of the model. The tactic evaluates compiled code, so the guarantee also assumes that the compiled code agrees with the definitions.

**Proposition (A rare counterexample is missed).** Let a property fail on exactly one of $N$ values, and let $k$ tests draw values independently and uniformly. The probability that no test finds the counterexample is $(1 - 1/N)^k \ge 1 - k/N$.

*Proof.* Each test misses with probability $1 - 1/N$, and the tests are independent, so all $k$ miss with probability $(1 - 1/N)^k$. Bernoulli's inequality $(1 - t)^k \ge 1 - kt$ for $0 \le t \le 1$ holds by induction on $k$: for $k = 0$ both sides are $1$, and $(1 - t)^{k+1} \ge (1 - kt)(1 - t) = 1 - (k+1)t + kt^2 \ge 1 - (k+1)t$, where the first step needs $1 - t \ge 0$. $\square$

### Examples

**Example (A bounded draw).** Take $lo = 3$ and $hi = 5$ in $\mathbb{N}$. The generator draws $z$ in `Fin 3`, so $z \in \{0, 1, 2\}$, and returns $3 + z \in \{3, 4, 5\}$. If the generator gives $z = 1$, the result is $4$ with the proofs $3 \le 4$ and $4 \le 5$. In $\mathbb{Z}$ with $lo = -2$ and $hi = 2$, the draw is $z \in [0, 4]$ and the result is $z - 2 \in [-2, 2]$. A random Boolean is a draw in `Fin 2` compared with $1$. Two dice in Lean:

```lean
def twoDice : RandT IO ℕ := do
  let a ← Random.rand (Fin 6)
  let b ← Random.rand (Fin 6)
  pure (a.val + b.val + 2)

#eval IO.runRandWith 42 twoDice
```

The second draw starts from the state that the first draw left, so the two values are not equal by force.

**Example (A random injective function).** At size $0$ the generator of `InjectiveFunction ℤ` takes the domain `Int.range (-2) 2`, the list $[-2, -1, 0, 1]$, and a random permutation of it, for example $[0, -2, 1, -1]$. The function sends $-2 \mapsto 0$, $-1 \mapsto -2$, $0 \mapsto 1$, $1 \mapsto -1$, and each other integer to itself, so $7 \mapsto 7$. It is injective by the corollary.

**Example (Shrinking an injective function).** Take the keys $[1, 2, 3]$ and the values $[3, 1, 2]$: $1 \mapsto 3$, $2 \mapsto 1$, $3 \mapsto 2$. The sizes of the removed blocks are `sliceSizes 3`, that is $3$ and then $\lfloor 3/2 \rfloor = 1$, and the sequence stops at $\lfloor 1/2 \rfloor = 0$. The block of size $3$ removes all keys and gives the identity. The blocks of size $1$ at the indices $0, 1, 2$ give the keys $[2, 3]$, $[1, 3]$, $[1, 2]$, and the values $[3, 1, 2]$ filtered to these keys are $[3, 2]$, $[3, 1]$, $[1, 2]$. So the three candidates are the swap $2 \leftrightarrow 3$, the swap $1 \leftrightarrow 3$ and the identity. They are not restrictions of the original function: $2 \mapsto 1$ is gone, as $1$ is no longer a key.

**Example (Shrinking numbers).** The shrinker of $\mathbb{N}$ lists the successive halves, so $5$ shrinks to $[2, 1, 0]$ and $4$ to $[2, 1, 0]$. The shrinker of $\mathbb{N}^{+}$ shrinks $m - 1$ and adds $1$: $6$ gives $[3, 2, 1]$. The shrinker of $\mathbb{Q}$ combines a shrunk numerator with a shrunk denominator. For $3/4$, the numerators are $1, -1, 0, 0$ (the halves $1, 0$ of $3$ with both signs) and the denominators are $2, 1, 0$, and the candidates are the quotients, $\tfrac12, 1, 0, -\tfrac12, -1$ and several zeros, as division by $0$ gives $0$ in `Rat.divInt`.

**Example (A finitely supported function).** Let $A = [\langle 1, 5 \rangle, \langle 2, 0 \rangle, \langle 1, 9 \rangle]$ with default $7$. As a total function, $1 \mapsto 5$ (the first pair wins), $2 \mapsto 0$ and $4 \mapsto 7$. After the change of default, $4 \mapsto 0$, the support is $\{1\}$, and the finitely supported function is $5$ at $1$ and $0$ elsewhere.

**Counterexample (A false statement that passes).** The statement $\forall x \colon \mathtt{UInt8},\ x < x + 1$ is false at $x = 255$, where $x + 1 = 0$. The test

```lean
example : ∀ x : UInt8, x < x + 1 := by
  plausible
```

reports no counterexample with the default configuration. It runs $100$ tests with the sizes $0, 1, \dots, 99$, and the generator of `UInt8` draws a value between $0$ and the current size. So no test draws $255$. A test with uniform draws would still miss with probability $(255/256)^{100} \approx 0.68$ by the proposition above. When `plausible` finds no counterexample it closes the goal with `sorry`, so the proof is not accepted as complete.

A false statement with many counterexamples is refuted at once: `∀ xs : List ℕ, xs.reverse = xs` fails on each list with two different entries, and after shrinking the report is a short list such as `[0, 1]`.

### The library around it

::: mathlib
`Random` · `Mathlib.Control.Random`

`Random m α` with `random`, and `BoundedRandom m α` with `randomR`, over `RandGT g m = StateT (ULift g) m`, with the special cases `RandG`, `RandT` and `Rand`. The steps are `Rand.next`, `Rand.split` and `Rand.range`, and the functions `Random.rand`, `Random.randBound`, `Random.randFin` and `Random.randBool`. Instances exist for `Fin n` with `NeZero n`, `Bool`, `ULift`, and bounded instances for `ℕ`, `ℤ` and `Fin n`. `IO.runRand` uses the global generator `stdGenRef`; the header warns that it is not seeded at the start of a program and is not local to a thread.

<?decl Random?>
:::

::: mathlib
`Plausible.InjectiveFunction` · `Mathlib.Testing.Plausible.Functions`

With `apply`, `InjectiveFunction.mk` from a list and a permutation, `injective`, the list lemmas `List.applyId_cons`, `List.applyId_zip_eq`, `List.applyId_eq_self`, `applyId_mem_iff` and `applyId_injective`, and the shrinker `shrink` with `shrinkPerm`, `Perm.slice` and `sliceSizes`. The instance `PiInjective.sampleableExt` samples `{f : ℤ → ℤ // Function.Injective f}`. The same file has `Injective.testable`, `Monotone.testable` and `Antitone.testable`, which test the definitions with their quantifiers unfolded.

<?decl Plausible.InjectiveFunction?>
:::

::: mathlib
`Plausible.TotalFunction.applyFinsupp` · `Mathlib.Testing.Plausible.Functions`

With `zeroDefault` and `zeroDefaultSupp`, and the instances `Finsupp.sampleableExt` and `DFinsupp.sampleableExt`. These instances cannot shrink the domain, as the comment in the source says, since `interp` has no inverse.

<?decl Plausible.TotalFunction.applyFinsupp?>
:::

::: mathlib
`Plausible.Rat.shrinkable` · `Mathlib.Testing.Plausible.Sampleable`

The shrinkers `Rat.shrinkable` and `PNat.shrinkable`, the generators `Rat.Arbitrary` (a numerator in $[-s, s]$ and a denominator in $[0, s]$ at size $s$) and `PNat.Arbitrary`, and the instances `Rat.sampleableExt` and `PNat.sampleableExt`. The file `Mathlib.Testing.Plausible.Testable` adds `Testable.factTestable`, which tests `Fact p` as `p`.

<?decl Plausible.Rat.shrinkable?>
:::

The index of this edition has no declaration for a statement on the distribution of the values of `Random.rand`: Mathlib does not prove that the draws are uniform or independent, and the proposition on missed counterexamples is a statement about an ideal generator.

Common errors of a learner: The first error is to leave `plausible` in a proof; it never proves a goal, and on success it closes the goal with `sorry`. The second error is to trust a passing test on a type with large values; the sizes are small by default, and a larger `maxSize` in the configuration reaches more values. The third error is to expect `Random.randFin` on `Fin 0`; it needs `NeZero n`. The fourth error is to expect different values from two runs of `IO.runRandWith` with the same seed; the generator is deterministic.

### Exercises

1. (A) List the values that the generator of `BoundedRandom ℤ` can return for $lo = -1$ and $hi = 3$, with the draw $z$ for each. Hint: $z \in [0, 4]$.
2. (A) Compute the shrinks of $9$ in $\mathbb{N}$ and of $9$ in $\mathbb{N}^{+}$. Hint: $9 \mapsto [4, 2, 1, 0]$ in $\mathbb{N}$.
3. (A) Compute `sliceSizes 6` and the number of candidates that `shrinkPerm` produces for a list of length $6$. Hint: the sizes are $6, 3, 1$, with $\lfloor 6/n \rfloor$ positions for size $n$.
4. (B) Prove `List.applyId_cons`: the function of $(y, z) :: xs$ sends $x$ to $z$ if $y = x$, and to the function of $xs$ at $x$ if not. Hint: unfold the lookup of the first pair.
5. (B) Let `xs = [1, 2]` and `ys = [1, 1]`. Show that `List.applyId (xs.zip ys)` is not injective, and say which hypothesis of the theorem fails. Hint: `xs` is not a permutation of `ys`.
6. (B) A property of `Fin 1000` fails on $10$ values. How many uniform independent tests make the probability of a miss less than $0.01$? Hint: solve $(0.99)^k < 0.01$; the answer is $459$.
7. (C) Let $\alpha$ be a finite type with $N$ elements and $\beta$ a decidable predicate on $\alpha$. Prove that $\forall x, \beta(x)$ is decidable, by a procedure that checks each element once. Explain why $N$ random draws can miss a counterexample while this procedure cannot, and compute the probability of a miss for $N = 3$ and one counterexample. Hint: random draws can repeat; the probability is $(2/3)^3 = 8/27$.

### Notes and history

Property based testing in the form used here comes from QuickCheck of Claessen and Hughes, 2000, for Haskell: random inputs from type classes, and shrinking of a counterexample. Mathlib had this tool as `slim_check`; it now lives in the library Plausible, and the files above add instances for Mathlib types. The design of the random monad follows the Haskell library `MonadRandom`, as the header of `Mathlib.Control.Random` says. Knuth treats the generation and the statistical tests of pseudorandom numbers in TAOCP.

The Mathlib files are by these authors, read from their headers: `Mathlib.Control.Random` by Henrik Böving, `Mathlib.Testing.Plausible.Functions` by Simon Hudon, and `Mathlib.Testing.Plausible.Sampleable` and `Mathlib.Testing.Plausible.Testable` by Henrik Böving and Simon Hudon.

### Reference

<?reference?>
