---
title: The archimedean property
kind: theory
modules:
  - Mathlib.Algebra.Order.Archimedean.Defs
  - Mathlib.Algebra.Order.Archimedean.Basic
  - Mathlib.Algebra.Order.Floor.Defs
  - Mathlib.Algebra.Order.CompleteField
explains:
  E3: [Archimedean, FloorRing, exists_rat_btwn]
  E2: [exists_nat_gt, archimedean_iff_nat_lt, exists_nat_one_div_lt, instArchimedeanRat, Real.instArchimedean, Archimedean.floorRing, Int.floor, Int.floor_le, Int.lt_floor_add_one, Int.floor_eq_iff, ConditionallyCompleteLinearOrderedField.inducedOrderRingHom, ConditionallyCompleteLinearOrderedField.inducedOrderRingIso]
  E1: auto
families: []
requires: [V06.C03, V04]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The archimedean property

### Overview

The previous section ordered the field $\mathbb{R}(x)$ so that $x$ is larger than every integer. The rationals and the reals have no such element: each of their elements is smaller than some natural number. This is the archimedean property. It separates the ordered fields of analysis from the larger ordered fields of algebra and of nonstandard analysis. This section defines the property, proves that $\mathbb{Q}$ and $\mathbb{R}$ have it, and proves that $\mathbb{R}(x)$ does not. In an archimedean ordered ring every element has an integer part, the floor, and Mathlib records this in the class `FloorRing`. With the floor the section proves that $\mathbb{Q}$ is dense in each archimedean ordered field. The section ends with the theorem that every archimedean ordered field embeds in $\mathbb{R}$, so that $\mathbb{R}$ is the largest archimedean ordered field.

### Definitions

**Definition (Archimedean).** An ordered additive commutative monoid $M$ is archimedean if for all $x, y \in M$ with $y > 0$ there is $n \in \mathbb{N}$ with $x \le n y$.

The definition says that no element is infinitely large compared to a positive element. For an ordered field the definition takes a simpler form, proved below: every element is smaller than some natural number.

**Definition (Floor and ceiling).** Let $R$ be a linearly ordered ring. A floor function on $R$ is a function $\lfloor \cdot \rfloor : R \to \mathbb{Z}$ such that for all $z \in \mathbb{Z}$ and $x \in R$,
$$z \le \lfloor x \rfloor \iff z \le x.$$
A ceiling function $\lceil \cdot \rceil : R \to \mathbb{Z}$ satisfies $\lceil x \rceil \le z \iff x \le z$.

In the language of Volume 4, the floor is the right adjoint of the inclusion $\mathbb{Z} \to R$ in a Galois connection, and the ceiling is its left adjoint. The condition with $z = \lfloor x \rfloor$ gives $\lfloor x \rfloor \le x$. The condition with $z = \lfloor x \rfloor + 1$ gives $x < \lfloor x \rfloor + 1$. Conversely these two inequalities determine $\lfloor x \rfloor$.

::: mathlib
`Archimedean` · `Mathlib.Algebra.Order.Archimedean.Defs`

`Archimedean M` is a `Prop` class over `[AddCommMonoid M] [PartialOrder M]`. Its field `Archimedean.arch` states `∀ x {y}, 0 < y → ∃ n : ℕ, x ≤ n • y`. The multiplication by `n` is the scalar action `n • y` of `ℕ` on the monoid, so the class makes sense for ordered groups with no multiplication. For an ordered field `K` one writes `[Field K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K]`.

<?decl Archimedean?>
:::

::: mathlib
`FloorRing` · `Mathlib.Algebra.Order.Floor.Defs`

`FloorRing R` is a class over `[Ring R] [LinearOrder R]`. It is data, not a `Prop`: it holds the functions `floor` and `ceil` and the two Galois connections. The user writes `Int.floor x` or `⌊x⌋` and `Int.ceil x` or `⌈x⌉`. The class is data so that a type can carry a floor function that computes. The instance on `ℚ` computes with numerators and denominators, and `norm_num` evaluates the floor of an explicit rational number.

<?decl FloorRing?>
:::

### Theorems and proofs

**Proposition (Forms of the archimedean property).** Let $K$ be an ordered field. The following are equivalent.

1. $K$ is archimedean.
2. For each $x \in K$ there is $n \in \mathbb{N}$ with $x < n$.
3. For each $\varepsilon > 0$ in $K$ there is $n \in \mathbb{N}$ with $1/(n+1) < \varepsilon$.

*Proof.* (1) implies (2). Apply the definition to $x$ and $y = 1 > 0$: there is $n$ with $x \le n \cdot 1 = n$. Then $x < n + 1$.

(2) implies (3). Let $\varepsilon > 0$. By (2) there is $n$ with $1/\varepsilon < n$, so $1/\varepsilon < n + 1$. Both sides are positive. Inversion reverses the inequality between positive elements, so $1/(n + 1) < \varepsilon$.

(3) implies (1). Let $x \in K$ and $y > 0$. If $x \le 0$, take $n = 0$. Suppose $x > 0$. Apply (3) to $\varepsilon = y / x > 0$: there is $n$ with $1/(n+1) < y/x$. Multiply by the positive element $(n+1) x$. This gives $x < (n+1) y$. $\square$

::: mathlib
`archimedean_iff_nat_lt` · `Mathlib.Algebra.Order.Archimedean.Basic`

The statement is `Archimedean K ↔ ∀ x : K, ∃ n : ℕ, x < n` for a linearly ordered field `K`. This is the equivalence of (1) and (2). The direction (1) to (2) is the lemma `exists_nat_gt`, which holds in each strict ordered semiring. The form (3) is `exists_nat_one_div_lt : 0 < ε → ∃ n : ℕ, 1 / (n + 1) < ε`.

<?decl archimedean_iff_nat_lt?>
:::

**Theorem ($\mathbb{Q}$ is archimedean).** For each $x \in \mathbb{Q}$ there is $n \in \mathbb{N}$ with $x < n$.

*Proof.* Write $x = m / k$ with $m \in \mathbb{Z}$ and $k \ge 1$. Then $x \le |m| / k \le |m| < |m| + 1$. Take $n = |m| + 1$. $\square$

**Theorem ($\mathbb{R}$ is archimedean).** For each $x \in \mathbb{R}$ there is $n \in \mathbb{N}$ with $x < n$.

*Proof.* Suppose not. Then some $x$ satisfies $n \le x$ for all $n \in \mathbb{N}$. The set $\mathbb{N} \subseteq \mathbb{R}$ is nonempty and bounded above by $x$. By the completeness of $\mathbb{R}$ it has a least upper bound $s$. The number $s - 1$ is not an upper bound, so there is $n \in \mathbb{N}$ with $s - 1 < n$. Then $s < n + 1$, and $n + 1 \in \mathbb{N}$. This contradicts the fact that $s$ is an upper bound of $\mathbb{N}$. $\square$

The proof uses only the completeness of the order. The same argument shows that every conditionally complete ordered field is archimedean.

::: mathlib
`Real.instArchimedean` · `Mathlib.Algebra.Order.Archimedean.Real.Basic`

The instance `Archimedean ℝ` lets lemmas such as `exists_nat_gt` apply to real numbers. The instance for the rationals is `instArchimedeanRat`, with `instArchimedeanInt` and `instArchimedeanNat` for the integers and the naturals. The general fact for complete fields is `ConditionallyCompleteLinearOrderedField.to_archimedean`.

<?decl Real.instArchimedean?>
:::

**Theorem (Existence of the floor).** Let $R$ be an archimedean strict linearly ordered ring. Each $x \in R$ has a unique integer $\lfloor x \rfloor$ with
$$\lfloor x \rfloor \le x < \lfloor x \rfloor + 1.$$

*Proof.* Let $S = \{z \in \mathbb{Z} : z \le x\}$. By the archimedean property there is $n \in \mathbb{N}$ with $-x < n$, so $-n < x$ and $-n \in S$. So $S$ is nonempty. There is also $m \in \mathbb{N}$ with $x < m$. Each $z \in S$ satisfies $z \le x < m$, so $S$ is bounded above by $m$. A nonempty set of integers that is bounded above has a largest element. Let $f$ be the largest element of $S$. Then $f \le x$. The integer $f + 1$ is not in $S$, so $x < f + 1$. This proves existence.

For uniqueness, let $f$ and $g$ be two integers with both properties. Then $f \le x < g + 1$, so $f < g + 1$, so $f \le g$. By symmetry $g \le f$. $\square$

The floor function so defined satisfies the Galois condition: if $z \le x$ then $z \in S$, so $z \le \lfloor x \rfloor$. If $z \le \lfloor x \rfloor$ then $z \le x$.

::: mathlib
`Archimedean.floorRing` · `Mathlib.Algebra.Order.Archimedean.Basic`

The definition `Archimedean.floorRing R : FloorRing R` builds a floor function from the archimedean property, by the proof above. It uses classical choice, so it does not compute. For this reason it is a `def` and not an instance: `ℝ` and `ℚ` have their own instances. The bare existence statement is `exists_floor`.

<?decl Archimedean.floorRing?>
:::

::: mathlib
`Int.floor_eq_iff` · `Mathlib.Algebra.Order.Floor.Ring`

The statement is `⌊a⌋ = z ↔ (z : R) ≤ a ∧ a < z + 1`. It is the usual way to compute a floor in a proof: guess $z$, then prove two inequalities. The two halves are `Int.floor_le : (⌊a⌋ : R) ≤ a` and `Int.lt_floor_add_one : a < ⌊a⌋ + 1`.

<?decl Int.floor_eq_iff?>
:::

**Theorem (Density of $\mathbb{Q}$).** Let $K$ be an archimedean ordered field and $x < y$ in $K$. There is $q \in \mathbb{Q}$ with $x < q < y$.

*Proof.* The element $y - x$ is positive. By the archimedean property there is an integer $n \ge 1$ with $n > 1/(y - x)$, so $n y - n x > 1$. Let $m = \lfloor n x \rfloor + 1$. By the floor theorem, $n x < m$ and $m - 1 \le n x$. So
$$n x < m \le n x + 1 < n y.$$
Divide by $n > 0$: $x < m / n < y$. Take $q = m/n$. $\square$

::: mathlib
`exists_rat_btwn` · `Mathlib.Algebra.Order.Archimedean.Basic`

The statement is `x < y → ∃ q : ℚ, x < q ∧ q < y` in a linearly ordered archimedean field. The rational number `q` appears in `K` through the coercion of the previous section. The lemma is the main tool to approximate real numbers by rationals.

<?decl exists_rat_btwn?>
:::

**Theorem ($\mathbb{R}(x)$ is not archimedean).** The ordered field $\mathbb{R}(x)$ of the previous section is not archimedean.

*Proof.* For each $n \in \mathbb{N}$ the polynomial $x - n$ has leading coefficient $1 > 0$, so $x > n$. Thus $x$ is not smaller than any natural number, and form (2) of the proposition fails. $\square$

The same element gives a failure of density: no rational number lies between $x$ and $x + 1$, since every rational is smaller than $x$.

**Theorem (Embedding in $\mathbb{R}$).** Let $K$ be an archimedean ordered field. There is a unique ring homomorphism $\iota : K \to \mathbb{R}$ that preserves the order. It is injective. If $K$ is also conditionally complete, then $\iota$ is an isomorphism.

The map sends $a \in K$ to the real number $\sup \{ q \in \mathbb{Q} : q < a \}$. The density theorem shows that the set is nonempty and bounded above, and that $\iota$ determines $a$. The proof that $\iota$ respects sums and products is a computation with rationals on both sides of $a$ and $b$. This section does not give it. The second claim says that $\mathbb{R}$ is the unique complete ordered field, up to a unique isomorphism.

::: mathlib
`ConditionallyCompleteLinearOrderedField.inducedOrderRingHom` · `Mathlib.Algebra.Order.CompleteField`

The definition takes an archimedean ordered field `α` and a conditionally complete ordered field `β`, and gives an ordered ring homomorphism `α →+*o β`. The construction uses `LinearOrderedField.cutMap`, the set of rationals below an element, and takes its supremum in `β`. When `α` is also conditionally complete, `ConditionallyCompleteLinearOrderedField.inducedOrderRingIso` is an ordered ring isomorphism `α ≃+*o β`.

<?decl ConditionallyCompleteLinearOrderedField.inducedOrderRingHom?>
:::

### Examples

**Example (Floors).** In $\mathbb{R}$, $\lfloor 2.7 \rfloor = 2$ and $\lceil 2.7 \rceil = 3$. For negative numbers the floor goes down: $\lfloor -2.5 \rfloor = -3$, since $-3 \le -2.5 < -2$. The ceiling is $\lceil -2.5 \rceil = -2$. For an integer $z$, $\lfloor z \rfloor = \lceil z \rceil = z$. For $\sqrt 2$, the inequalities $1 \le \sqrt 2 < 2$ follow from $1 \le 2 < 4$, so $\lfloor \sqrt 2 \rfloor = 1$. In general $\lceil x \rceil = -\lfloor -x \rfloor$.

**Example (A rational between $\sqrt 2$ and $1.415$).** Follow the proof of density with $x = \sqrt 2$ and $y = 1.415$. From $1.4143^2 = 2.00024449 > 2$ follows $\sqrt 2 < 1.4143$, so $y - x > 0.0007$. Then $1/(y - x) < 1/0.0007 < 1429$, and $n = 1429$ works. Next compute $\lfloor 1429 \sqrt 2 \rfloor$. Since $2 \cdot 1429^2 = 4084082$ and $2020^2 = 4080400 < 4084082 < 4084441 = 2021^2$, the floor is $2020$. So $m = 2021$ and $q = 2021/1429$. Check: $2021^2 = 4084441 > 4084082 = 2 \cdot 1429^2$, so $q > \sqrt 2$. And $1.415 \cdot 1429 = 2022.035 > 2021$, so $q < 1.415$. In decimals $q \approx 1.414276$.

**Counterexample (A non-archimedean ordered field).** In $\mathbb{R}(x)$ the element $1/x$ is a positive infinitesimal, as the previous section showed. So form (3) of the proposition fails for $\varepsilon = 1/x$: each $1/(n+1)$ is a positive real number, and every positive real number is larger than $1/x$. The field has no floor function either. A floor $\lfloor x \rfloor = z$ would give $x < z + 1$ with $z + 1 \in \mathbb{Z}$, which is false.

### The library around it

Lemmas on the floor function live in `Mathlib.Algebra.Order.Floor.Defs`, `Mathlib.Algebra.Order.Floor.Ring` and `Mathlib.Algebra.Order.Floor.Semiring`. For a semiring such as `ℕ` or the nonnegative reals there is a separate class `FloorSemiring` with the function `Nat.floor`, written `⌊x⌋₊`. The fractional part is `Int.fract x = x - ⌊x⌋`, with values in $[0, 1)$. The tactic `norm_num` evaluates floors of explicit rational numbers. The hyperreal numbers of nonstandard analysis are in Volume 15, as the type `Hyperreal` with an infinite element `Hyperreal.omega` and an infinitesimal `Hyperreal.epsilon`.

**Common errors of a learner.**

- Confusing the floor with truncation toward zero. The floor of $-2.5$ is $-3$, not $-2$. The truncation of $-2.5$ is $-2$.
- Using `Archimedean.floorRing` as an instance on `ℝ`. It would give a second floor function and a conflict of instances. Use the existing instance.
- Assuming that every ordered field is archimedean. The field $\mathbb{R}(x)$ and the hyperreals are not.
- Forgetting the hypothesis $y > 0$ in the definition. With $y = 0$, $n y = 0$ for each $n$, and the statement fails for every $x > 0$.
- Writing `⌊x⌋` and expecting a natural number. `Int.floor` has values in `ℤ`; `Nat.floor` has values in `ℕ`.

### Exercises

1. (A) Compute $\lfloor -7/3 \rfloor$, $\lceil -7/3 \rceil$, $\lfloor \sqrt{10} \rfloor$ and $\lfloor 100/7 \rfloor$. Justify each by the two inequalities.
2. (A) Show that $\lfloor x + z \rfloor = \lfloor x \rfloor + z$ for $z \in \mathbb{Z}$. Hint: check the two inequalities that define the floor.
3. (A) Show that $\mathbb{Z}$ is archimedean as an ordered additive group.
4. (B) Show that in an archimedean ordered field, for each $a > 1$ and each $M$ there is $n$ with $a^n > M$. Hint: write $a = 1 + h$ and use $(1 + h)^n \ge 1 + n h$.
5. (B) Show that $\lfloor 2x \rfloor = \lfloor x \rfloor + \lfloor x + 1/2 \rfloor$ in $\mathbb{R}$. Hint: split into the cases $\operatorname{fract} x < 1/2$ and $\operatorname{fract} x \ge 1/2$.
6. (B) Show that $\mathbb{Q}(\sqrt 2)$, with the order of $\mathbb{R}$, is an archimedean ordered field. Show that it is not conditionally complete. Hint: the set of its elements below $\sqrt 3$.
7. (B) Show that the lexicographic order on $\mathbb{Z} \times \mathbb{Z}$, with $(a, b) > 0$ if $a > 0$, or $a = 0$ and $b > 0$, makes it an ordered group that is not archimedean.
8. (C) Show that the map $\iota$ of the embedding theorem preserves the order: $a < b$ in $K$ implies $\iota(a) < \iota(b)$. Hint: by density there are two rationals between $a$ and $b$.
9. (C) Show that an ordered field that contains an infinite element also contains a positive infinitesimal, and conversely. Hint: inversion.

### Notes and history

The property carries the name of Archimedes, who stated it in *On the sphere and cylinder* as an axiom on magnitudes. It is older: Eudoxus used it in his theory of proportion, which survives as Book V of Euclid's *Elements*. Otto Stolz gave the name "archimedean" in the 1880s, and Hilbert used it as an axiom of geometry in 1899. Hölder proved in 1901 that every archimedean ordered group embeds in $(\mathbb{R}, +)$. Hahn generalised this in 1907: every ordered abelian group embeds in a group of formal power series with real coefficients and well-ordered support, ordered lexicographically. These Hahn series also give large non-archimedean ordered fields. Robinson's hyperreal numbers (1961) and Conway's surreal numbers (1976) are two further non-archimedean ordered fields. The surreal numbers contain every ordered field, since each ordered field embeds in them. This handbook does not treat surreal numbers.

### Reference

<?reference?>
