---
title: The unit disc and the upper half-plane as types
kind: api
modules:
  - Mathlib.Analysis.Complex.UnitDisc.Basic
  - Mathlib.Analysis.Complex.UpperHalfPlane.Basic
  - Mathlib.Analysis.Complex.UpperHalfPlane.Topology
  - Mathlib.Analysis.Complex.IntegerCompl
explains:
  E2: [Complex.UnitDisc, Complex.UnitClosedDisc, Complex.UnitDisc.coe_circle_smul, Complex.UnitDisc.tendsto_pow_atTop_nhds_zero, UpperHalfPlane, UpperHalfPlane.ρ, UpperHalfPlane.ofComplex, UpperHalfPlane.verticalStrip, UpperHalfPlane.subset_verticalStrip_of_isCompact, Complex.integerComplement]
  E1: auto
families: []
requires: [V19.C01, V19.C03, V13]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The unit disc and the upper half-plane as types

### Overview

The open unit disc $\mathbb{D} = \{z \in \mathbb{C} : |z| < 1\}$ and the upper half-plane $\mathbb{H} = \{z \in \mathbb{C} : \operatorname{Im} z > 0\}$ are the two standard models of a simply connected proper domain of $\mathbb{C}$. The Cayley map $z \mapsto (z - i)/(z + i)$ sends $\mathbb{H}$ onto $\mathbb{D}$, so the two domains are biholomorphic. Each model has its advantages. The disc is bounded, and the Schwarz lemma of Chapter 3 lives on it. The half-plane carries the action of $\mathrm{SL}(2, \mathbb{R})$ by Möbius maps, and the theory of modular forms lives on it.

In Mathlib, both domains are types and not only sets. A point of `UpperHalfPlane` is a structure with a complex number and a proof that its imaginary part is positive. A point of `Complex.UnitDisc` is a complex number with a proof that its norm is less than $1$. A function on the type has no junk values off the domain, and a lemma about the point can use the proof that it carries. The price is a coercion to $\mathbb{C}$ at each step of a computation.

This section describes the two types, their algebraic structure, their topology, and the bridge back to functions on $\mathbb{C}$. It also describes the complement of the integers in $\mathbb{C}$, a domain that contains $\mathbb{H}$ and on which the partial fraction expansions of trigonometric functions live. Section 2 adds the Möbius action, the hyperbolic metric, the invariant measure and the expansion at the cusp.

The section is mostly about definitions. The mathematics is elementary: products of points of $\mathbb{D}$ stay in $\mathbb{D}$, positive dilations and real translations preserve $\mathbb{H}$, and $\mathbb{H}$ is convex and so contractible. The interest is in the form of the statements, which the later sections and the modular forms of Volume 12 use without change.

### The library around it

#### The unit disc

`Complex.UnitDisc` is the open ball of radius $1$ about $0$ in $\mathbb{C}$, as a type, with the scoped notation $\mathbb{D}$. The constructor `Complex.UnitDisc.mk` takes a complex number $z$ and a proof of $\|z\| < 1$, and the coercion to $\mathbb{C}$ is injective by `Complex.UnitDisc.coe_injective`. The basic bound is `Complex.UnitDisc.norm_lt_one`. Its consequences `Complex.UnitDisc.coe_ne_one` and `Complex.UnitDisc.one_add_coe_ne_zero` are the facts that a computation with $(1 + z)/(1 - z)$ or with $\log(1 - z)$ needs.

The type has the structure that the ball has. The product of two points of the disc is in the disc, so `Complex.UnitDisc` is a commutative semigroup with zero, with the cancellation law and the negation. It has no $1$, because $1$ is not in the open disc. For this reason the power uses an exponent in $\mathbb{N}^+$ and not in $\mathbb{N}$: `Complex.UnitDisc.coe_pow` computes $(z^n : \mathbb{C}) = z^n$ for $n \ge 1$. The theorem `Complex.UnitDisc.tendsto_pow_atTop_nhds_zero` says that $z^n \to 0$ for each $z$ in the disc. The real and imaginary parts and the conjugation are also defined on the type, and conjugation makes it a star semigroup.

The circle group acts on the disc by rotation. The action is the instance `Complex.UnitDisc.instMulActionCircle`, and `Complex.UnitDisc.coe_circle_smul` computes $(u \cdot z : \mathbb{C}) = u z$ for $u$ in `Circle`. The rotations are the automorphisms of $\mathbb{D}$ that fix $0$, by the Schwarz lemma, and this action is the first piece of the automorphism group.

`Complex.UnitClosedDisc` is the closed ball of radius $1$. It contains $1$, so it is a monoid with zero, and its power uses an exponent in $\mathbb{N}$. Its bound is `Complex.UnitClosedDisc.norm_le_one`. The closed disc acts on the open disc by multiplication, and `Complex.UnitClosedDisc.coe_closedBall_smul` computes the action. So a point of the closed disc times a point of the open disc stays in the open disc, which is the fact behind most estimates on Blaschke products.

#### The upper half-plane

`UpperHalfPlane` is a structure with two fields: the complex number `UpperHalfPlane.coe` and the proof `UpperHalfPlane.coe_im_pos` that its imaginary part is positive. The scoped notation is `ℍ`. The functions `UpperHalfPlane.re` and `UpperHalfPlane.im` give the two parts, `UpperHalfPlane.im_pos` gives the bound $0 < \operatorname{Im} z$, and `UpperHalfPlane.ext_re_im` gives equality from equal parts. Each point is nonzero by `UpperHalfPlane.ne_zero`, and it is not real by `UpperHalfPlane.ne_ofReal`. The theorem `UpperHalfPlane.mem_slitPlane` puts each point in the slit plane, so the principal logarithm and the complex powers of Chapter 1 are holomorphic near it.

Two points have names. `UpperHalfPlane.I` is the point $i$. `UpperHalfPlane.ρ` is the point $\rho = -1/2 + i\sqrt{3}/2$, a primitive cube root of unity. The theorem `UpperHalfPlane.ρ_sq` gives $\rho^2 = -\rho - 1$, and `UpperHalfPlane.norm_ρ` gives $|\rho| = 1$. The points $i$ and $\rho$ are the two elliptic points of the modular group.

Two simple actions preserve $\mathbb{H}$. The positive reals act by dilation, through the instance `UpperHalfPlane.posRealAction`, and `UpperHalfPlane.pos_real_im` computes $\operatorname{Im}(t z) = t \operatorname{Im} z$. The reals act by translation as an additive action, with the notation $x +_v z$, and `UpperHalfPlane.vadd_re` and `UpperHalfPlane.vadd_im` compute the parts. The translations $z \mapsto z + n$ for integers $n$ are the action of the matrix $T$ of the modular group, and the periodicity of a modular form is a statement about this action.

#### The topology of the half-plane

The topology on `UpperHalfPlane` is the subspace topology from $\mathbb{C}$. The coercion is an open embedding by `UpperHalfPlane.isOpenEmbedding_coe`, so a property of $\mathbb{C}$ near a point of $\mathbb{H}$ transfers to $\mathbb{H}$. The instances give a second countable, normal, locally compact, noncompact and contractible space. The contractibility comes from the convexity of $\mathbb{H}$.

The bridge to functions on $\mathbb{C}$ is `UpperHalfPlane.ofComplex`, an open partial homeomorphism from $\mathbb{C}$ to $\mathbb{H}$ whose source is the open set $\{\operatorname{Im} z > 0\}$. It is the inverse of the coercion on its source. The theorem `UpperHalfPlane.ofComplex_apply_of_im_pos` evaluates it there, and `UpperHalfPlane.ofComplex_apply_of_im_nonpos` shows that off the source it takes one fixed junk value. For $f : \mathbb{H} \to \mathbb{C}$, the composition $f \circ \mathrm{ofComplex}$ is a function on $\mathbb{C}$ that agrees with $f$ on $\mathbb{H}$, by `UpperHalfPlane.comp_ofComplex`. Mathlib uses this composition to say that $f$ is holomorphic: it asks that $f \circ \mathrm{ofComplex}$ is differentiable on the open set $\{\operatorname{Im} z > 0\}$. The theorem `UpperHalfPlane.periodic_comp_ofComplex` transfers a period under real translation to the composition.

The vertical strips are the sets `UpperHalfPlane.verticalStrip` $A$ $B$ of points with $|\operatorname{Re} z| \le A$ and $\operatorname{Im} z \ge B$. The theorem `UpperHalfPlane.subset_verticalStrip_of_isCompact` puts each compact set inside a strip with $B > 0$. A uniform estimate on all strips is thus a locally uniform estimate on $\mathbb{H}$, and this is how the convergence of Eisenstein series is proved.

#### The complement of the integers

`Complex.integerComplement` is the set $\mathbb{C} \setminus \mathbb{Z}$. The partial fraction expansion $\pi \cot \pi z = 1/z + \sum_{n \ge 1} 2z/(z^2 - n^2)$ holds on it, so the lemmas give the denominators that this expansion has. The theorem `Complex.integerComplement_add_ne_zero` gives $z + n \ne 0$ for each integer $n$, and `Complex.integerComplement_pow_two_ne_pow_two` gives $z^2 \ne n^2$. The set contains $\mathbb{H}$ by `UpperHalfPlane.coe_mem_integerComplement`, so a series that converges on $\mathbb{C} \setminus \mathbb{Z}$ also converges on $\mathbb{H}$.

#### Common errors

1. The power on `Complex.UnitDisc` takes an exponent in $\mathbb{N}^+$, because the open disc has no $1$. A statement with $z^0$ does not type check, and a statement with $z^n$ for a natural number $n$ needs a cast to `PNat` first.
2. The value of `UpperHalfPlane.ofComplex` at a point with $\operatorname{Im} z \le 0$ is a junk point of $\mathbb{H}$, not an error. A lemma about $f \circ \mathrm{ofComplex}$ is useful only on the open set $\{\operatorname{Im} z > 0\}$, so check that the point is there.
3. The coercion from `UpperHalfPlane` to $\mathbb{C}$ is a function, and a goal often has $(z : \mathbb{C}).\mathrm{im}$ where a lemma has `UpperHalfPlane.im` $z$. The theorem `UpperHalfPlane.coe_im` rewrites one to the other.

### Exercises

1. (A) Show that the product of two points of the open unit disc is in the open disc, and that the product of a point of the closed disc and a point of the open disc is in the open disc.
2. (A) Show from `UpperHalfPlane.ρ_sq` that $\rho^3 = 1$ and $\rho \ne 1$.
3. (A) Show that $-1/z$ is in $\mathbb{H}$ for each $z$ in $\mathbb{H}$, with the formula $\operatorname{Im}(-1/z) = \operatorname{Im} z / |z|^2$.
4. (B) Show that the Cayley map $z \mapsto (z - i)/(z + i)$ sends $\mathbb{H}$ into $\mathbb{D}$, and find its inverse.
5. (B) Prove `UpperHalfPlane.subset_verticalStrip_of_isCompact`: a compact set has a bounded real part and an imaginary part bounded below by a positive number, because $\operatorname{Im}$ is continuous and positive on it.
6. (C) Show that $\sum_{n \in \mathbb{Z}} 1/(z + n)^2$ converges locally uniformly on $\mathbb{C} \setminus \mathbb{Z}$, and that the sum is holomorphic and has period $1$.

### Reference

<?reference?>
