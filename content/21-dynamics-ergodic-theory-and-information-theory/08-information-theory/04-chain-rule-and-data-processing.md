---
title: The chain rule and the data processing inequality
kind: theory
modules:
  - Mathlib.InformationTheory.KullbackLeibler.ChainRule
  - Mathlib.InformationTheory.KullbackLeibler.DataProcessing
explains:
  E3: [InformationTheory.klDiv_compProd_eq_add, InformationTheory.klDiv_compProd_left, InformationTheory.klDiv_map_le, InformationTheory.klDiv_trim_le, InformationTheory.klDiv_comp_right_le]
  E2: [InformationTheory.integrable_llr_compProd_iff, InformationTheory.integral_llr_compProd_eq_add, InformationTheory.integrable_llr_of_integrable_llr_compProd, InformationTheory.klDiv_map_of_ac, InformationTheory.toReal_klDiv_trim_of_ac, InformationTheory.integrable_llr_map, ConvexOn.map_condExp_rnDeriv_le, ConvexOn.comp_rnDeriv_map_le, ConvexOn.comp_rnDeriv_trim_le]
  E1: auto
families: []
requires: [V18.C04, V20.C06, V20.C08]
reads_with: []
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## The chain rule and the data processing inequality

### Overview

The data processing inequality says that no processing of the data, by a measurable map or by a noisy channel, can increase the Kullback-Leibler divergence. The chain rule splits the divergence of two joint laws into a part for the first coordinates and a part for the conditional laws. Together they make the divergence additive on products. This section uses $\varphi(x) = x \log x + 1 - x$ and the integral form of Section 3, and the conditional expectation and kernels of Volume 20.

### Definitions

Here $\mu$ and $\nu$ are finite measures on $(X, \mathcal{A})$.

**Definition (Restriction to a sub-σ-algebra).** For a σ-algebra $\mathcal{G} \subseteq \mathcal{A}$, $\mu|_{\mathcal{G}}$ is the measure $\mu$ on the sets of $\mathcal{G}$ only. In Mathlib it is `μ.trim hm`, with `hm : m ≤ m𝓧`.

**Definition (Composition with a kernel).** For a Markov kernel $\kappa$ from $X$ to $Y$, $\mu \otimes \kappa$ is the measure on $X \times Y$ with $(\mu \otimes \kappa)(A \times B) = \int_A \kappa_x(B) \, d\mu(x)$. Its first marginal is $\mu$, because $\kappa_x(Y) = 1$. Its second marginal is the measure $\kappa \circ \mu$, with $(\kappa \circ \mu)(B) = \int \kappa_x(B) \, d\mu(x)$.

::: mathlib
`MeasureTheory.Measure.bind` · `Mathlib.MeasureTheory.Measure.GiryMonad`

`μ.bind κ` is the measure $\kappa \circ \mu$. It is the second marginal of `μ.compProd κ` (`Measure.snd_compProd`). A constant kernel gives the product measure: `μ.compProd (Kernel.const α ν) = μ.prod ν` (`Measure.compProd_const`).

<?decl MeasureTheory.Measure.bind?>
:::

### Theorems and proofs

**Lemma (Density on a sub-σ-algebra).** If $\mu \ll \nu$ with $f = d\mu/d\nu$, then $\mu|_{\mathcal{G}} \ll \nu|_{\mathcal{G}}$ with density $E_\nu[f \mid \mathcal{G}]$, the conditional expectation for the finite measure $\nu$.

*Proof.* For $B \in \mathcal{G}$, $\int_B E_\nu[f \mid \mathcal{G}] \, d\nu = \int_B f \, d\nu = \mu(B)$. This function is $\mathcal{G}$-measurable. $\square$

::: mathlib
`MeasureTheory.rnDeriv_trim` · `Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym`

`(μ.trim hm).rnDeriv (ν.trim hm) =ᵐ[ν.trim hm] fun x ↦ ENNReal.ofReal (ν[fun x ↦ (μ.rnDeriv ν x).toReal | m] x)`, for `μ ≪ ν`.

<?decl MeasureTheory.rnDeriv_trim?>
:::

**Lemma (Conditional Jensen for $\varphi$).** If $f \ge 0$ and $\varphi(f)$ is $\nu$-integrable, then $\varphi(E_\nu[f \mid \mathcal{G}]) \le E_\nu[\varphi(f) \mid \mathcal{G}]$ $\nu$-a.e.

*Proof.* For rational $q > 0$, the tangent line $\ell_q(x) = \varphi(q) + \log q \, (x - q)$ lies below $\varphi$ on $[0, \infty)$, because $\varphi$ is convex there. For $x > 0$, $\sup_q \ell_q(x) = \varphi(x)$ by continuity, and $\ell_q(0) = 1 - q$, so $\sup_q \ell_q(0) = 1 = \varphi(0)$. The conditional expectation is linear, monotone and fixes constants. So $\ell_q(E_\nu[f \mid \mathcal{G}]) = E_\nu[\ell_q(f) \mid \mathcal{G}] \le E_\nu[\varphi(f) \mid \mathcal{G}]$ a.e. for each $q$. There are countably many $q$, so the bounds hold together a.e. Take the supremum over $q$. $\square$

::: mathlib
`ConvexOn.map_condExp_rnDeriv_le` · `Mathlib.InformationTheory.KullbackLeibler.DataProcessing`

For a strongly measurable `f : ℝ → ℝ`, convex on `Ici 0` and continuous within `Ici 0` at `0`, with `fun x ↦ f (μ.rnDeriv ν x).toReal` integrable: `f (ν[(dμ/dν) | m]) ≤ᵐ[ν.trim hm] ν[f (dμ/dν) | m]`. `comp_rnDeriv_trim_le` and `comp_rnDeriv_map_le` put the density of the restricted or image measures on the left. The general form is `ConvexOn.map_condExp_le`.

<?decl ConvexOn.map_condExp_rnDeriv_le?>
:::

**Theorem (Data processing for a sub-σ-algebra).** $\mathrm{KL}(\mu|_{\mathcal{G}} \,\|\, \nu|_{\mathcal{G}}) \le \mathrm{KL}(\mu \,\|\, \nu)$.

*Proof.* Assume the right side is finite. Then $\mu \ll \nu$ and, by the integral form of Section 3, $\varphi(f)$ is $\nu$-integrable with $\mathrm{KL}(\mu \,\|\, \nu) = \int \varphi(f) \, d\nu$. Put $\bar f = E_\nu[f \mid \mathcal{G}]$. By the two lemmas, $0 \le \varphi(\bar f) \le E_\nu[\varphi(f) \mid \mathcal{G}]$ a.e., so $\varphi(\bar f)$ is integrable, and
$$\int \varphi(\bar f) \, d\nu \le \int E_\nu[\varphi(f) \mid \mathcal{G}] \, d\nu = \int \varphi(f) \, d\nu.$$
As $\varphi(\bar f)$ is $\mathcal{G}$-measurable, the integral form for the restricted measures makes the left side $\mathrm{KL}(\mu|_{\mathcal{G}} \,\|\, \nu|_{\mathcal{G}})$. $\square$

::: mathlib
`InformationTheory.klDiv_trim_le` · `Mathlib.InformationTheory.KullbackLeibler.DataProcessing`

`klDiv (μ.trim hm) (ν.trim hm) ≤ klDiv μ ν`, for finite measures, with no other hypothesis. The real value for `μ ≪ ν` is `toReal_klDiv_trim_of_ac`.

<?decl InformationTheory.klDiv_trim_le?>
:::

**Corollary (Data processing for a map).** For a measurable map $g : X \to Y$, $\mathrm{KL}(g_*\mu \,\|\, g_*\nu) \le \mathrm{KL}(\mu \,\|\, \nu)$.

*Proof.* Let $\mathcal{G} = \{g^{-1}(B)\}$, the σ-algebra generated by $g$. As $\mu(g^{-1}(B)) = g_*\mu(B)$, a density $h$ of $g_*\mu$ for $g_*\nu$ gives the density $h \circ g$ of $\mu|_{\mathcal{G}}$ for $\nu|_{\mathcal{G}}$, and conversely each $\mathcal{G}$-measurable density has the form $h \circ g$. By the change of variables formula, $\int \varphi(h) \, d(g_*\nu) = \int \varphi(h \circ g) \, d\nu$, and absolute continuity transfers the same way. So $\mathrm{KL}(g_*\mu \,\|\, g_*\nu) = \mathrm{KL}(\mu|_{\mathcal{G}} \,\|\, \nu|_{\mathcal{G}})$, and the theorem applies. $\square$

::: mathlib
`InformationTheory.klDiv_map_le` · `Mathlib.InformationTheory.KullbackLeibler.DataProcessing`

`Measurable g → klDiv (μ.map g) (ν.map g) ≤ klDiv μ ν`. For `μ ≪ ν` with integrable `llr`, `klDiv_map_of_ac` gives the value through `ν[· | MeasurableSpace.comap g m𝓨]`, and `integrable_llr_map` transfers the integrability.

<?decl InformationTheory.klDiv_map_le?>
:::

**Theorem (Chain rule).** For finite measures $\mu, \nu$ on $X$ and Markov kernels $\kappa, \eta$ from $X$ to $Y$,
$$\mathrm{KL}(\mu \otimes \kappa \,\|\, \nu \otimes \eta) = \mathrm{KL}(\mu \,\|\, \nu) + \mathrm{KL}(\mu \otimes \kappa \,\|\, \mu \otimes \eta)$$
in $[0, \infty]$.

*Proof.* Step 1, absolute continuity. Taking first marginals, $\mu \otimes \kappa \ll \nu \otimes \eta$ gives $\mu \ll \nu$. It also gives $\mu \otimes \kappa \ll \mu \otimes \eta$: let $(\mu \otimes \eta)(A) = 0$, let $f = d\mu/d\nu$ and $S = \{f > 0\}$. Then $\mu(X \setminus S) = 0$, and $\nu$ restricted to $S$ is absolutely continuous for $\mu$, since $\mu(B \cap S) = \int_{B \cap S} f \, d\nu$. As $\eta_x(A_x) = 0$ for $\mu$-a.e. $x$, also for $\nu$-a.e. $x \in S$, so $(\nu \otimes \eta)(A \cap (S \times Y)) = 0$. So $(\mu \otimes \kappa)(A \cap (S \times Y)) = 0$ by hypothesis, and $(\mu \otimes \kappa)(A) \le \mu(X \setminus S) = 0$. Conversely $\mu \ll \nu$ gives $\mu \otimes \eta \ll \nu \otimes \eta$, and absolute continuity is transitive. If it fails, both sides are $\infty$.

Step 2, the densities. Assume the three relations, and let $g = d(\mu \otimes \kappa)/d(\mu \otimes \eta)$. As $\mu = f \cdot \nu$, $\mu \otimes \eta = (f \circ \mathrm{pr}_1) \cdot (\nu \otimes \eta)$. So $F(x, y) = f(x)\, g(x, y)$ is the density of $\mu \otimes \kappa$ for $\nu \otimes \eta$. Both factors are positive $(\mu \otimes \kappa)$-a.e., and $\log F = \log f \circ \mathrm{pr}_1 + \log g$ there.

Step 3, integrability. If $\log f$ and $\log g$ are integrable, then so is $\log F$, and its integral is the sum; $\int \log f \circ \mathrm{pr}_1 \, d(\mu \otimes \kappa) = \int \log f \, d\mu$ because the first marginal is $\mu$. The mass terms are $\nu(X) - \mu(X)$ on the left, and $\nu(X) - \mu(X)$ and $0$ on the right. If $\log F$ is integrable, the corollary for $\mathrm{pr}_1$ gives $\mathrm{KL}(\mu \,\|\, \nu) < \infty$. So $\log f \circ \mathrm{pr}_1$ is integrable, and $\log g = \log F - \log f \circ \mathrm{pr}_1$ is too. So the two sides are finite together, and then equal. $\square$

::: mathlib
`InformationTheory.klDiv_compProd_eq_add` · `Mathlib.InformationTheory.KullbackLeibler.ChainRule`

`klDiv (μ.compProd κ) (ν.compProd η) = klDiv μ ν + klDiv (μ.compProd κ) (μ.compProd η)`, with `[IsMarkovKernel κ] [IsMarkovKernel η]`. Step 2 is `ProbabilityTheory.rnDeriv_compProd`, step 3 `integrable_llr_compProd_iff`, `integrable_llr_of_integrable_llr_compProd` and `integral_llr_compProd_eq_add`.

<?decl InformationTheory.klDiv_compProd_eq_add?>
:::

**Corollary (One kernel).** $\mathrm{KL}(\mu \otimes \kappa \,\|\, \nu \otimes \kappa) = \mathrm{KL}(\mu \,\|\, \nu)$.

*Proof.* The second term of the chain rule is $\mathrm{KL}(\mu \otimes \kappa \,\|\, \mu \otimes \kappa) = 0$. $\square$

**Corollary (Data processing for a channel).** $\mathrm{KL}(\kappa \circ \mu \,\|\, \kappa \circ \nu) \le \mathrm{KL}(\mu \,\|\, \nu)$.

*Proof.* $\kappa \circ \mu$ is the image of $\mu \otimes \kappa$ under the second projection. Apply the corollary for maps, then the corollary for one kernel. $\square$

::: mathlib
`InformationTheory.klDiv_comp_right_le` · `Mathlib.InformationTheory.KullbackLeibler.DataProcessing`

`klDiv (μ.bind κ) (ν.bind κ) ≤ klDiv μ ν` for a Markov kernel `κ`. The corollary for one kernel is `klDiv_compProd_left`, in the chain rule file.

<?decl InformationTheory.klDiv_comp_right_le?>
:::

**Corollary (Products).** For probability measures, $\mathrm{KL}(P \otimes P' \,\|\, Q \otimes Q') = \mathrm{KL}(P \,\|\, Q) + \mathrm{KL}(P' \,\|\, Q')$. So $\mathrm{KL}(P^{\otimes n} \,\|\, Q^{\otimes n}) = n\, \mathrm{KL}(P \,\|\, Q)$.

*Proof.* A product is a composition with a constant kernel, so the chain rule gives $\mathrm{KL}(P \,\|\, Q) + \mathrm{KL}(P \otimes P' \,\|\, P \otimes Q')$. Data processing in both directions shows that the swap of coordinates keeps the divergence, so $\mathrm{KL}(P \otimes P' \,\|\, P \otimes Q') = \mathrm{KL}(P' \otimes P \,\|\, Q' \otimes P) = \mathrm{KL}(P' \,\|\, Q')$ by the corollary for one kernel. Induction on $n$ ends the proof. $\square$

The index of this edition has no declaration for the divergence of product measures; the swap is `Measure.prod_swap`.

### Examples

**Example (A noisy channel).** Take $\mu = \mathrm{Bern}(\frac12)$ and $\nu = \mathrm{Bern}(\frac14)$, with $\mathrm{KL}(\mu \,\|\, \nu) = \frac12 \log \frac43 \approx 0.1438$. Send each through the binary symmetric channel that flips the bit with probability $\frac14$. The output laws are $\mathrm{Bern}(\frac12)$ and $\mathrm{Bern}(\frac38)$, because $\frac14 \cdot \frac34 + \frac34 \cdot \frac14 = \frac38$. Then
$$\mathrm{KL}(\kappa \circ \mu \,\|\, \kappa \circ \nu) = \tfrac12 \log \tfrac{4}{3} + \tfrac12 \log \tfrac{4}{5} = \tfrac12 \log \tfrac{16}{15} \approx 0.0323,$$
which is smaller.

**Example (A constant map).** Let $g$ map $X$ to one point. Then $g_*\mu = \mu(X)\,\delta$ and $g_*\nu = \nu(X)\,\delta$, and $\mathrm{KL}(g_*\mu \,\|\, g_*\nu) = \mu(X) \log \frac{\mu(X)}{\nu(X)} + \nu(X) - \mu(X)$ for $\nu(X) > 0$. So data processing contains the mass bound of Section 3.

### The library around it

Common errors of a learner:

- The chain rule has $\mathrm{KL}(\mu \otimes \kappa \,\|\, \mu \otimes \eta)$ as its second term, a divergence of joint laws. The index of this edition has no declaration for its form $\int \mathrm{KL}(\kappa_x \,\|\, \eta_x) \, d\mu(x)$.
- The kernels must be Markov. For finite kernels the marginals change and the mass terms do not match.
- `klDiv_map_le` needs a measurable `g`. If `g` is not even a.e. measurable, `Measure.map g μ` is the junk value `0`.

### Exercises

1. (A) Show that $\mathrm{KL}(g_*\mu \,\|\, g_*\nu) = \mathrm{KL}(\mu \,\|\, \nu)$ for a measurable bijection $g$ with measurable inverse.
2. (B) Let $A_1, \ldots, A_k$ be a measurable partition of $X$. Show that $\mathrm{KL}(\mu \,\|\, \nu) \ge \sum_i \mu(A_i) \log \frac{\mu(A_i)}{\nu(A_i)} + \nu(X) - \mu(X)$, with the conventions $0 \log 0 = 0$ and a term $\infty$ when $\nu(A_i) = 0 < \mu(A_i)$. Hint: map $X$ to $\{1, \ldots, k\}$.
3. (B) Show that equality holds in the corollary for maps when $d\mu/d\nu = h \circ g$ for a measurable $h$.
4. (B) For finite $X$ and $Y$, show that $\mathrm{KL}(\mu \otimes \kappa \,\|\, \mu \otimes \eta) = \sum_x \mu(\{x\})\, \mathrm{KL}(\kappa_x \,\|\, \eta_x)$.
5. (C) Prove that for probability weights $t_1, \ldots, t_k$, $\mathrm{KL}(\sum_i t_i \mu_i \,\|\, \sum_i t_i \nu_i) \le \sum_i t_i\, \mathrm{KL}(\mu_i \,\|\, \nu_i)$. Assume all $\mu_i, \nu_i$ are probability measures. Hint: use the kernels $i \mapsto \mu_i$, $i \mapsto \nu_i$ on $\{1, \ldots, k\}$ and the second projection.

### Notes and history

Kullback and Leibler studied the divergence together with sufficient statistics, for which equality holds in data processing. The chain rule is the analogue of the chain rule for Shannon entropy.

### Reference

<?reference?>
