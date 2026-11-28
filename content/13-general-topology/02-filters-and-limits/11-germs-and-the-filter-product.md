---
title: Germs and the filter product
kind: api
modules:
  - Mathlib.Order.Filter.Germ.Basic
  - Mathlib.Order.Filter.Germ.OrderedMonoid
  - Mathlib.Order.Filter.FilterProduct
  - Mathlib.Order.Filter.Ring
explains:
  E2: [Filter.Germ, Filter.Germ.coe_eq, Filter.Germ.const, Filter.Germ.map, Filter.Germ.compTendsto, Filter.Germ.coe_tendsto, Filter.Germ.liftRel_coe, Filter.Germ.coe_le, Filter.Germ.coe_lt, Filter.EventuallyLE.mul_le_mul]
  E1: auto
families: []
requires: [V04, V05, V06, V13.C01]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Germs and the filter product

### Overview

Many statements about a function along a filter do not depend on the values of the function outside a large set. Two functions that agree eventually have the same limits, the same eventual bounds and the same eventual signs. The germ of $f$ along $l$ is the class of $f$ for this relation. The type `Filter.Germ l β` is the quotient of $\alpha \to \beta$ by eventual equality along $l$. The operations of $\beta$ pass to the germs pointwise, so the germs form a group, a ring or an ordered module when $\beta$ does.

For an ultrafilter $\varphi$, the germs along $\varphi$ are the ultrapower of $\beta$. In this case each order on $\beta$ that is linear gives a linear order on the germs, and a field gives a field. Volume 15 uses this construction for the hyperreal numbers, and Volume 32 uses its dependent form for ultraproducts in model theory. The module `Mathlib.Order.Filter.Ring` gives the rules for eventual inequalities in an ordered ring, which are the facts behind the ordered ring of germs.

### The library around it

#### The type of germs

The setoid `Filter.germSetoid l β` is eventual equality along $l$, and `Filter.Germ l β` is its quotient. The coercion sends a function $f$ to its germ, written `↑f`. Two germs of functions are equal if and only if the functions are eventually equal (`Filter.Germ.coe_eq`), and `Filter.EventuallyEq.germ_eq` is the direction that is used in a proof. Each germ is the germ of a function, so a proof about all germs can start with `Filter.Germ.inductionOn`, with the forms for two and three germs.

The constant germ `Filter.Germ.const b` is the germ of the constant function $b$. If $l$ is proper, then two constants have the same germ only if they are equal (`Filter.Germ.const_inj`). If $l = \bot$, then all functions are eventually equal and the type of germs has one element, so this hypothesis is necessary.

| Lean name | Statement |
|---|---|
| `Filter.Germ.coe_eq` | $\uparrow f = \uparrow g \iff f =ᶠ[l] g$ |
| `Filter.Germ.const_inj` | for proper $l$, $\uparrow a = \uparrow b \iff a = b$ |
| `Filter.Germ.map_coe` | $\mathrm{map}\ \mathrm{op}\ \uparrow f = \uparrow(\mathrm{op} \circ f)$ |
| `Filter.Germ.coe_compTendsto` | the germ of $f$ composed with $g$ is the germ of $f \circ g$ |
| `Filter.Germ.coe_tendsto` | $\uparrow f$ tends to $l_b$ if and only if $f$ does |
| `Filter.Germ.liftPred_coe` | $\mathrm{LiftPred}\ p\ \uparrow f \iff \forall^f x \in l,\ p(f(x))$ |
| `Filter.Germ.liftRel_coe` | $\mathrm{LiftRel}\ r\ \uparrow f\ \uparrow g \iff \forall^f x \in l,\ r(f(x), g(x))$ |

#### Maps and composition

A map $op : \beta \to \gamma$ acts on germs by composition: `Filter.Germ.map op` sends the germ of $f$ to the germ of $op \circ f$. The binary form `Filter.Germ.map₂` takes two germs. These two operations give all the algebraic operations below. A germ can also be composed on the right. If $g : \gamma \to \alpha$ tends from $l_c$ to $l$, then `Filter.Germ.compTendsto` sends the germ of $f$ along $l$ to the germ of $f \circ g$ along $l_c$. The tendsto hypothesis is needed for the definition to respect eventual equality: if $f =ᶠ[l] f'$, then $f \circ g =ᶠ[l_c] f' \circ g$ because $g$ sends a large set of $l_c$ into the set where $f$ and $f'$ agree. The rule `Filter.Tendsto.congr_germ` states this fact.

The limits of a germ are well defined: `Filter.Germ.Tendsto` says that a germ tends to a filter, and `Filter.Germ.coe_tendsto` says that this holds for $\uparrow f$ if and only if $f$ tends to the filter. A germ is constant, `Filter.Germ.IsConstant`, if it is the germ of a constant function.

#### Predicates and relations

A predicate $p$ on $\beta$ lifts to germs: `Filter.Germ.LiftPred p g` says that $p$ holds eventually for a representative. A relation $r$ lifts in the same way with `Filter.Germ.LiftRel`. The order on germs is the lift of the order on $\beta$ (`Filter.Germ.le_def`), so `Filter.Germ.coe_le` says that $\uparrow f \le \uparrow g$ if and only if $f \le ᶠ[l] g$. This order is a partial order when $\beta$ has one, and a lattice when $\beta$ is a lattice, with the supremum computed pointwise. The bottom and top of $\beta$ give the bottom and top of the germs.

#### Algebraic structure

The module `Mathlib.Order.Filter.Germ.Basic` gives the instances for each algebraic class: `Filter.Germ.instMonoid`, `Filter.Germ.instCommRing`, `Filter.Germ.instModule` and many more. Each operation is pointwise on representatives, so the coercion is a homomorphism: `Filter.Germ.coe_mul` says $\uparrow(f g) = \uparrow f \uparrow g$, and `Filter.Germ.coeRingHom` packs the coercion as a ring homomorphism. For a proper filter and a nontrivial ring, the ring of germs is nontrivial (`Filter.Germ.instNontrivial`).

The module `Mathlib.Order.Filter.Germ.OrderedMonoid` gives the ordered forms, such as `Filter.Germ.instIsOrderedMonoid` and `Filter.Germ.instCanonicallyOrderedAdd`. The module `Mathlib.Order.Filter.Ring` gives `Filter.Germ.instIsOrderedRing`. Its proof rests on rules for eventual inequalities that are useful on their own:

- `Filter.EventuallyLE.add_le_add`: $f_1 \le ᶠ f_2$ and $g_1 \le ᶠ g_2$ give $f_1 + g_1 \le ᶠ f_2 + g_2$.
- `Filter.EventuallyLE.mul_le_mul`: with $0 \le ᶠ g_1$ and $0 \le ᶠ f_2$, the same rule holds for products.
- `Filter.EventuallyLE.mul_nonneg`: $0 \le ᶠ f$ and $0 \le ᶠ g$ give $0 \le ᶠ f g$.
- `Filter.eventually_sub_nonneg`: $0 \le ᶠ g - f$ if and only if $f \le ᶠ g$.

Each rule is the pointwise rule applied on the intersection of two large sets.

#### Ultrapowers

The module `Mathlib.Order.Filter.FilterProduct` treats the germs along an ultrafilter $\varphi$. Here an ultrafilter decides each property, so more structure passes from $\beta$ to the germs.

**Proposition.** If $\beta$ is a field, then the germs along an ultrafilter form a field.

*Proof sketch.* Let $\uparrow f$ be a nonzero germ. Then the set $\{x : f(x) = 0\}$ is not in $\varphi$, so its complement is in $\varphi$, because $\varphi$ is an ultrafilter. Define $g(x) = f(x)^{-1}$. Then $f g = 1$ on this complement, so $\uparrow f \uparrow g = 1$. $\square$

This is `Filter.Germ.instField`, with `Filter.Germ.instDivisionRing`. In the same way, a linear order on $\beta$ gives a linear order on the germs (`Filter.Germ.instLinearOrder`): of the two sets $\{f \le g\}$ and $\{g < f\}$, one is in $\varphi$. The strict order is computed pointwise only for an ultrafilter: `Filter.Germ.coe_lt` says that $\uparrow f < \uparrow g$ if and only if eventually $f(x) < g(x)$. A linear ordered field such as $\mathbb{R}$ gives an ordered field of germs (`Filter.Germ.instIsStrictOrderedRing`), and the hyperreals are this field for the hyperfilter on $\mathbb{N}$.

The type `Filter.Product l ε` is the dependent form: the quotient of $\prod_a \varepsilon(a)$ by eventual equality, through the setoid `Filter.productSetoid`.

#### Common errors

1. For a filter that is not an ultrafilter, the order on germs is not linear, and $\uparrow f < \uparrow g$ is not the same as eventually $f < g$. The rule `Filter.Germ.coe_lt` needs an ultrafilter.
2. The germs along $\bot$ form a type with one element. A lemma such as `Filter.Germ.const_inj` needs the hypothesis `l.NeBot`.
3. The definition `Filter.Germ.compTendsto` takes a proof that the map tends to the filter. A rewrite that changes the map must also change this proof, so use `Filter.Germ.coe_compTendsto` to compute on representatives.

### Exercises

1. (A) Prove `Filter.Germ.coe_eq` from the definition of the quotient.
2. (A) Prove `Filter.EventuallyLE.add_le_add` from `Filter.EventuallyLE` and the pointwise rule.
3. (B) Show that the germs at $0$ of real functions, along `𝓝 0`, do not form a linear order.
4. (B) Show that the germs along `atTop` of functions $\mathbb{N} \to \mathbb{R}$ form a ring that is not a field.
5. (B) Show that along an ultrafilter the germ of $f$ tends to $b$ in $\mathbb{R}$ only if $f$ tends to $b$ along the ultrafilter, and give an example of a bounded sequence whose germ along a free ultrafilter has a limit while the sequence does not converge.
6. (C) Let $\varphi$ be a free ultrafilter on $\mathbb{N}$. Show that the germ of $n \mapsto n$ is greater than each constant germ, so the ordered field of germs is not Archimedean.

### Reference

<?reference?>
