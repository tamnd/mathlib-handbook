---
title: Normal functions and fixed points
kind: theory
modules:
  - Mathlib.SetTheory.Ordinal.FixedPoint
  - Mathlib.SetTheory.Ordinal.Enum
  - Mathlib.SetTheory.Ordinal.Topology
  - Mathlib.SetTheory.Ordinal.FixedPointApproximants
explains:
  E3: [Ordinal.nfp, Ordinal.deriv, Ordinal.enumOrd, Ordinal.isClosed_iff_iSup, OrdinalApprox.lfpApprox]
  E2: [Ordinal.iSup_iterate_eq_nfp, Ordinal.nfp_fp, Ordinal.nfp_le_fp, Ordinal.not_bddAbove_fp, Ordinal.deriv_zero_right, Ordinal.deriv_add_one, Ordinal.deriv_limit, Ordinal.isNormal_deriv, Ordinal.deriv_fp, Ordinal.mem_range_deriv, Ordinal.deriv_eq_enumOrd, Ordinal.nfp_add_zero, Ordinal.deriv_add_eq_mul_omega0_add, Ordinal.nfp_mul_one, Ordinal.enumOrd_strictMono, Ordinal.range_enumOrd, Ordinal.isNormal_enumOrd, Ordinal.mem_closure_tfae, OrdinalApprox.lfpApprox_add_one, OrdinalApprox.lfpApprox_ord_eq_lfp]
  E1: auto
families: []
requires: [V04.C04, V13.C01, V31.C02, V31.C03]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Normal functions and fixed points

### Overview

Chapter 3 found three maps $\beta \mapsto \alpha + \beta$, $\alpha \beta$ and $\alpha^\beta$ that are strictly increasing and continuous at limits. Such maps are the normal functions. Each normal function has fixed points above each ordinal, and its fixed points are again the values of a normal function, the derivative. This is the engine behind the epsilon numbers and the Veblen hierarchy of Section 2. The section also gives the order topology of the ordinals, in which "continuous at limits" is continuity and "closed" means "closed under suprema", the enumeration of a class of ordinals, and the transfinite iteration that finds the least fixed point of a monotone map on a complete lattice without continuity.

### Definitions

**Definition (Normal function).** A map $f$ from the ordinals to the ordinals is *normal* if it is strictly increasing and, for each limit $\lambda$, $f(\lambda) = \sup_{\beta < \lambda} f(\beta)$.

::: mathlib
`Order.IsNormal` · `Mathlib.Order.IsNormal`

`IsNormal f` is a structure for a map `f : α → β` between linear orders, with the fields `strictMono` and `mem_lowerBounds_upperBounds_of_isSuccLimit`: at a limit `a`, `f a` is below each upper bound of `f '' Iio a`. The form `Order.isNormal_iff : IsNormal f ↔ StrictMono f ∧ ∀ o, IsSuccLimit o → ∀ a, (∀ b < o, f b ≤ a) → f o ≤ a` is the definition of the text. The lemmas `IsNormal.comp` and `IsNormal.map_iSup` give composition and the preservation of bounded suprema. `Order.isNormal_iff_strictMono_and_continuous` in `Mathlib.Topology.Order.IsNormal` turns the condition into continuity for well-orders with the order topology.

<?decl Order.IsNormal?>
:::

A normal $f$ satisfies $\beta \le f(\beta)$, by induction: $\beta + 1 \le f(\beta) + 1 \le f(\beta + 1)$ at successors, and $\lambda = \sup_{\beta < \lambda} \beta \le f(\lambda)$ at limits. Also $f(\lambda)$ is a limit when $\lambda$ is, since $f(\beta) < f(\beta + 1)$ for each $\beta < \lambda$. Each nonempty set of ordinals that is bounded has a supremum (Chapter 2), and for such a set $T$ with no maximum, $\sup T$ is a limit and $f(\sup T) = \sup_{\tau \in T} f(\tau)$.

**Definition (Fixed points, next fixed point, derivative).** Let $f$ be normal. A *fixed point* of $f$ is an $\alpha$ with $f(\alpha) = \alpha$. Set $\operatorname{nfp}_f(a) = \sup_n f^n(a)$. The *derivative* $f'$ is defined by recursion:
$$f'(0) = \operatorname{nfp}_f(0), \qquad f'(\beta + 1) = \operatorname{nfp}_f(f'(\beta) + 1), \qquad f'(\lambda) = \sup_{\beta < \lambda} f'(\beta).$$

::: mathlib
`Ordinal.nfp` · `Mathlib.SetTheory.Ordinal.FixedPoint`

`nfp f a` is defined for any `f : Ordinal → Ordinal`, as the special case `nfpFamily fun _ : Unit => f` of the next fixed point of a family. `nfpFamily f a = ⨆ l, List.foldr f a l` runs over all finite words in the maps of the family, so that the result is a common fixed point. `iSup_iterate_eq_nfp f a : ⨆ n, f^[n] a = nfp f a` is the formula of the text. Most lemmas on families need `[Small.{u} ι]`, so that the supremum exists in `Ordinal.{u}`.

<?decl Ordinal.nfp?>
:::

::: mathlib
`Ordinal.deriv` · `Mathlib.SetTheory.Ordinal.FixedPoint`

`deriv f` is `derivFamily fun _ : Unit => f`, defined by `limitRecOn` with the three clauses of the text: `deriv_zero_right`, `deriv_add_one` and `deriv_limit`. `isNormal_deriv f` holds for every `f`; the hypothesis that `f` is normal enters only in `deriv_fp (H : IsNormal f) o : f (deriv f o) = deriv f o` and in `mem_range_deriv (H : IsNormal f) : a ∈ range (deriv f) ↔ f a = a`.

<?decl Ordinal.deriv?>
:::

**Definition (Enumeration).** Let $s$ be a class of ordinals that is not bounded. Its *enumeration* $e_s$ is defined by recursion: $e_s(\beta)$ is the least element of $s$ that is greater than $e_s(\gamma)$ for all $\gamma < \beta$.

::: mathlib
`Ordinal.enumOrd` · `Mathlib.SetTheory.Ordinal.Enum`

`enumOrd s o = sInf (s ∩ {b | ∀ c < o, enumOrd s c < b})`, defined by well-founded recursion for every set `s`. For an unbounded `s`, `enumOrd_strictMono`, `enumOrd_mem` and `range_enumOrd` say that it is an increasing bijection onto `s`; `enumOrdOrderIso` is the order isomorphism `Ordinal ≃o s`. For a strictly increasing `f`, `enumOrd_range` gives `enumOrd (range f) = f`. In Lean a "class" of ordinals is a `Set Ordinal.{u}`, a set in a larger universe.

<?decl Ordinal.enumOrd?>
:::

**Definition (Closed, club).** A class $s$ of ordinals is *closed* if $\sup T \in s$ for each nonempty bounded $T \subseteq s$. It is *club* if it is closed and not bounded.

### Theorems and proofs

**Theorem (Fixed point lemma).** Let $f$ be normal and $a$ an ordinal. Then $\operatorname{nfp}_f(a)$ is the least fixed point of $f$ that is $\ge a$. So the fixed points of $f$ are not bounded.

*Proof.* Let $a_n = f^n(a)$ and $\sigma = \sup_n a_n$. Since $a \le f(a)$, induction gives $a_n \le a_{n+1}$. If $a_n = a_{n+1}$ for some $n$, then $a_n$ is a fixed point and $\sigma = a_n$. Otherwise the $a_n$ increase strictly, $T = \{a_n\}$ has no maximum, and $f(\sigma) = \sup_n f(a_n) = \sup_n a_{n+1} = \sigma$. In both cases $a = a_0 \le \sigma$. If $b \ge a$ is a fixed point, then $a_n \le f^n(b) = b$ by monotonicity, so $\sigma \le b$. For the last claim, $\operatorname{nfp}_f(a)$ is a fixed point above $a$, for each $a$. $\square$

**Theorem (Derivative).** Let $f$ be normal. Then $f'$ is normal, and its values are exactly the fixed points of $f$. So $f'$ is the enumeration of the fixed points of $f$.

*Proof.* The map $f'$ is strictly increasing: $f'(\beta + 1) \ge f'(\beta) + 1$, and at limits $f'(\beta) < f'(\beta + 1) \le f'(\lambda)$; induction on $\gamma$ gives $f'(\beta) < f'(\gamma)$ for $\beta < \gamma$, as for the power in Chapter 3. Continuity is the limit clause. The values are fixed points, by induction: at $0$ and at successors by the fixed point lemma, and at a limit $\lambda$ because $f'(\lambda) = \sup T$ for the set $T$ of the fixed points $f'(\beta)$, $\beta < \lambda$, which has no maximum, so $f(\sup T) = \sup_{\tau \in T} f(\tau) = \sup T$.

Let $x$ be a fixed point, and let $o$ be the least ordinal with $x \le f'(o)$; it exists because $x \le f'(x)$. If $o = 0$, then $f'(0) = \operatorname{nfp}_f(0) \le x$ by the lemma. If $o = \xi + 1$, then $f'(\xi) < x$, so $f'(\xi) + 1 \le x$ and $f'(o) = \operatorname{nfp}_f(f'(\xi) + 1) \le x$. If $o$ is a limit, $f'(\xi) < x$ for all $\xi < o$, and $f'(o) \le x$. So $x = f'(o)$. A strictly increasing map onto $s$ is the enumeration of $s$, by induction on the argument. $\square$

Mathlib has the last step as `deriv_eq_enumOrd (H : IsNormal f) : deriv f = enumOrd (fixedPoints f)`.

**Theorem (Normal functions and clubs).** Let $s$ be a class of ordinals that is not bounded. Then $e_s$ is normal if and only if $s$ is closed. The range of a normal function is club.

*Proof.* The map $e_s$ is strictly increasing by its definition, and its values are all of $s$: if $x \in s$ is not a value, let $\beta$ be least with $e_s(\beta) > x$ (it exists since $e_s(x) \ge x$ and $x$ is not a value); then $x$ is greater than all $e_s(\gamma)$, $\gamma < \beta$, so $e_s(\beta) \le x$, a contradiction. Let $s$ be closed and $\lambda$ a limit. The supremum $\sigma = \sup_{\beta < \lambda} e_s(\beta)$ is in $s$, and $\sigma > e_s(\beta)$ for each $\beta < \lambda$, since $e_s(\beta) < e_s(\beta + 1) \le \sigma$. So $e_s(\lambda) \le \sigma$, and the converse inequality holds by monotonicity.

Now let $f$ be normal with range $s$, and let $T = \{f(\beta) : \beta \in U\}$ be nonempty and bounded. Let $\gamma = \sup U$; it exists because $\beta \le f(\beta)$. If $\gamma \in U$, then $\sup T = f(\gamma)$. Otherwise $U$ has no maximum, and $\sup T = f(\gamma)$ by continuity. So $s$ is closed. If $e_s$ is normal, $s$ is its range, so $s$ is closed. $\square$

::: mathlib
`Ordinal.isClosed_iff_iSup` · `Mathlib.SetTheory.Ordinal.Topology`

The ordinals carry the order topology (`Ordinal.instOrderTopology`). `isClosed_iff_iSup` says that `s` is closed if and only if `⨆ i, f i ∈ s` for each nonempty `ι : Type u` and `f : ι → Ordinal` with values in `s`: this is the closedness of the text. `mem_closure_tfae` lists five forms of `a ∈ closure s`, one of them `(s ∩ Iic a).Nonempty ∧ sSup (s ∩ Iic a) = a`. The enumeration theorem is `isNormal_enumOrd`, with closedness stated for bounded nonempty subsets. The old names `IsAcc`, `IsClosedBelow` and `enumOrd_isNormal_iff_isClosed` are deprecated.

<?decl Ordinal.isClosed_iff_iSup?>
:::

**Proposition (Closure in the order topology).** For a class $s$ and an ordinal $a$: $a$ is in the closure of $s$ if and only if $s \cap [0, a]$ is nonempty with supremum $a$. So $s$ is closed in the order topology if and only if it is closed in the sense of the definition.

*Proof.* The point $0$ is isolated, as $\{0\} = [0, 1)$. For $a > 0$ the intervals $(b, a]$ with $b < a$ form a base of neighbourhoods of $a$ in the order topology (Volume 13, Chapter 1), since $(b, a] = (b, a + 1)$. Let $t = s \cap [0, a]$. If each $(b, a]$ meets $s$, then $t$ is nonempty, and $\sup t$ is $\le a$ and $> b$ for each $b < a$, so $\sup t = a$. If $\sup t = a$ and $a \notin s$, then each $b < a$ is below some element of $t$, so $(b, a]$ meets $s$. For $a = 0$ both sides say $0 \in s$. The second claim follows: a closed $s$ contains $\sup T$ for bounded nonempty $T \subseteq s$, since $\sup T$ is in the closure of $T$ by the first claim; conversely, if $s$ is closed under suprema, each point of the closure is $\sup t \in s$. $\square$

**Theorem (Fixed points by transfinite iteration).** Let $L$ be a complete lattice, $g : L \to L$ monotone, and $x \le g(x)$. Define $x_0 = x$, $x_{\beta + 1} = g(x_\beta)$ and $x_\lambda = \sup_{\beta < \lambda} x_\beta$. The $x_\beta$ increase, and there is an ordinal $\beta$ with $x_\beta = x_{\beta + 1}$. Then $x_\beta$ is the least fixed point of $g$ that is $\ge x$.

*Proof.* Induction gives $x_\beta \le x_\gamma$ for $\beta \le \gamma$: at successors, $x_\beta \le x_{\beta+1}$ by induction from $x \le g(x)$ and monotonicity, and at limits by the definition of the supremum. If $x_\beta < x_{\beta + 1}$ for all $\beta$, then $\beta \mapsto x_\beta$ is injective on all the ordinals of the universe of $L$. Its range is a subset of $L$, so the ordinals would be in bijection with a set, a contradiction with the theorem of Burali-Forti (Chapter 2). So $x_\beta = x_{\beta+1} = g(x_\beta)$ for some $\beta$. If $y \ge x$ is a fixed point, induction gives $x_\gamma \le y$ for all $\gamma$: $x_{\gamma+1} = g(x_\gamma) \le g(y) = y$. $\square$

::: mathlib
`OrdinalApprox.lfpApprox` · `Mathlib.SetTheory.Ordinal.FixedPointApproximants`

`lfpApprox f x a = x ⊔ ⨆ b < a, f (lfpApprox f x b)` for `f : α →o α` on a complete lattice. The `⊔ x` makes the definition uniform: `lfpApprox_zero`, `lfpApprox_add_one (hx : x ≤ f x)` and `lfpApprox_of_isSuccLimit` give the three clauses. Mathlib bounds the stage: `lfpApprox_ord_eq_lfp : lfpApprox f ⊥ (ord (succ #α)) = f.lfp`. The proof uses `Cardinal.not_injective_limitation_set`, the cardinal form of the argument above, which Chapter 5 supports. `nextFixed_eq_iSup_lfpApprox` treats a general start `x`, and `gfpApprox` is the dual.

<?decl OrdinalApprox.lfpApprox?>
:::

### Examples

**Example (Fixed points of addition).** Let $f(\beta) = a + \beta$ with $a > 0$. The iterates from $0$ are $0, a, a \cdot 2, a \cdot 3, \ldots$, so $\operatorname{nfp}_f(0) = \sup_n a n = a \omega$. The fixed points are the $\beta$ with $a + \beta = \beta$, which are the $\beta \ge a \omega$ (Chapter 3, Section 1, Exercise 4). Each such $\beta$ is $a \omega + \gamma$ for a unique $\gamma$, so $f'(\gamma) = a\omega + \gamma$. In Mathlib these are `nfp_add_zero a : nfp (a + ·) 0 = a * ω` and `deriv_add_eq_mul_omega0_add a b : deriv (a + ·) b = a * ω + b`.

**Example (Fixed points of multiplication).** Let $f(\beta) = a \beta$ with $a > 1$. Then $0$ is a fixed point, and from $1$ the iterates are $1, a, a^2, \ldots$, so $\operatorname{nfp}_f(1) = \sup_n a^n = a^\omega$. This is `nfp_mul_one (ha : 0 < a) : nfp (a * ·) 1 = a ^ ω`. The fixed points are the multiples $a^\omega \delta$ (`mul_eq_right_iff_opow_omega0_dvd`), and `deriv_mul_eq_opow_omega0_mul` gives $f'(\delta) = a^\omega \delta$.

**Counterexample (Continuity is needed).** The map $f(\beta) = \beta + 1$ is strictly increasing and has no fixed point. It is not normal: $f(\omega) = \omega + 1$, but $\sup_n f(n) = \omega$. The iterates from $0$ have supremum $\omega$, which is not a fixed point. So the fixed point lemma needs continuity.

**Example (The transfinite iteration of Volume 4).** Volume 4, Chapter 4, Section 2 shows that Kleene's theorem fails on $P = \mathbb{N} \cup \{\omega, \omega + 1\}$ with $g(n) = n + 1$ and $g(\omega) = g(\omega + 1) = \omega + 1$. The transfinite iteration from $\bot = 0$ gives $x_n = n$, $x_\omega = \omega$, $x_{\omega + 1} = g(\omega) = \omega + 1$ and $x_{\omega + 2} = \omega + 1$. It stops at the stage $\omega + 1$ with the least fixed point $\omega + 1$.

### The library around it

The fixed point files work with families, since Section 2 needs common fixed points: `nfpFamily`, `derivFamily` and `not_bddAbove_fp_family` take `f : ι → Ordinal → Ordinal` with `[Small.{u} ι]`. For one map, `nfp_le_fp (H : Monotone f) (ab : a ≤ b) (h : f b ≤ b)` is the leastness, `nfp_fp (H : IsNormal f)` the fixed point property, and `not_bddAbove_fp` the unboundedness.

Common errors of a learner:

- `nfp f a` is defined for every `f`, but is a fixed point only for a normal `f`, as the counterexample shows.
- `enumOrd s` is junk for a bounded `s`. The lemmas need `¬ BddAbove s`.
- A "class" of ordinals is a `Set Ordinal.{u}`; the bounded subsets of it are small, which `Ordinal.bddAbove_iff_small` states.
- The stage of `lfpApprox_ord_eq_lfp` is a cardinal bound, not the least stage.

### Exercises

1. (A) Show that the composition of two normal functions is normal, and that $\beta \mapsto \omega^\beta + \beta$ is normal.
2. (A) Find the least fixed point of $\beta \mapsto \omega + \beta$ greater than $\omega^2$.
3. (A) Show that the intersection of two closed classes is closed. Give an unbounded class that is not closed.
4. (B) Show that the fixed points of $\beta \mapsto \omega^\beta$ form a club class, and that its least element is $\varepsilon_0$ of Chapter 3.
5. (B) Let $f$ be normal. Show that $f'(\beta) \ge f(\beta)$ for all $\beta$, and that $f' = f$ fails for $f(\beta) = 1 + \beta$.
6. (B) Prove that the intersection of two clubs is a club. Hint: from $\alpha$, alternate between the two classes $\omega$ times.
7. (C) Show that $\beta \mapsto e_s(\beta)$ is continuous at a limit $\lambda$ if and only if $\sup_{\beta < \lambda} e_s(\beta) \in s$.
8. (C) Let $L$ be the subsets of $\mathbb{N} \cup \{\omega\}$ with $g(X) = \{0\} \cup \{n + 1 : n \in X\} \cup \{\omega : \mathbb{N} \subseteq X\}$. Compute the stage at which the transfinite iteration stops.

### Notes and history

Normal functions and their derivatives are due to Veblen, *Continuous increasing functions of finite and transfinite ordinals* (1908). The fixed point lemma is in Jech, *Set Theory*, Chapter 8, and in Kunen, *Set Theory*, Chapter I, with clubs, which Chapter 6 of this volume studies for cofinality.

### Reference

<?reference?>
