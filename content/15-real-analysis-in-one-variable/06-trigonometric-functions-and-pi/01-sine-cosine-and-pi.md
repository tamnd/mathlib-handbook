---
title: Sine, cosine and the number pi
kind: theory
modules:
  - Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
  - Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
explains:
  E3: [Real.pi, Real.sin_eq_zero_iff, Real.hasDerivAt_sin]
  E2: [Real.exists_cos_eq_zero, Real.cos_pi_div_two, Real.sin_pi, Real.sin_periodic, Real.sin_antiperiodic, Real.sin_pos_of_pos_of_lt_pi, Real.pi_pos, Real.hasDerivAt_cos, Real.tendsto_sin_div_nhdsNE_zero, Real.strictAntiOn_cos, Real.cos_eq_one_iff]
  E1: auto
families: []
requires: [V02, V13, V15.C02, V15.C03, V15.C05]
reads_with: ["MIL"]
lean: []
mathlib: e54979a532247ae4eb9d5578a8fd40a1bc332101
status: drafted
drafted_by: writer@claude-opus-5-5
reviewed_by: []
---

## Sine, cosine and the number pi

### Overview

A first course meets sine and cosine in a right triangle and $\pi$ as the ratio of circumference to diameter. Neither description is a definition in analysis, because the length of an arc needs integration. Analysis reverses the order. This section follows the route of Mathlib: $\sin$ and $\cos$ come from the complex exponential of Chapter 5, the identities come from $e^{z+w} = e^z e^w$, two estimates from the series give $\cos 1 > 0$ and $\cos 2 < 0$, and $\pi$ is twice the zero of $\cos$ in $[1, 2]$. From that definition the section proves periodicity, the description of the zeros of $\sin$, and the derivatives $\sin' = \cos$, $\cos' = -\sin$.

### Definitions

**Definition (Complex sine and cosine).** For $z \in \mathbb{C}$ put
$$\cos z = \frac{e^{iz} + e^{-iz}}{2}, \qquad \sin z = \frac{e^{iz} - e^{-iz}}{2i}.$$

Insert $iz$ and $-iz$ into the series $e^z = \sum_{n \ge 0} z^n/n!$. The even terms survive in the sum and the odd terms in the difference:
$$\cos z = \sum_{k \ge 0} \frac{(-1)^k z^{2k}}{(2k)!}, \qquad \sin z = \sum_{k \ge 0} \frac{(-1)^k z^{2k+1}}{(2k+1)!}.$$
For real $x$ every term is real, so $\cos$ and $\sin$ restrict to functions $\mathbb{R} \to \mathbb{R}$. The series show that $\cos$ is even, $\sin$ is odd, $\cos 0 = 1$ and $\sin 0 = 0$.

::: mathlib
`Real.sin` · `Mathlib.Analysis.Complex.Trigonometric`

`Real.sin x = (Complex.sin x).re`, with `Complex.sin z = (exp (-z * I) - exp (z * I)) * I / 2`, the formula above without a division by $i$. The cast lemma `Complex.ofReal_sin` moves between the two. `Real.cos` has the same form.

<?decl Real.sin?>
:::

**Definition (The number pi).** The real number $\pi$ is $2c$, where $c$ is the unique zero of $\cos$ in $[1, 2]$.

The theorem (A zero of cosine) below proves that the zero exists and is unique.

::: mathlib
`Real.pi` · `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`

`Real.pi` is `2 * Classical.choose exists_cos_eq_zero`, where `Real.exists_cos_eq_zero : 0 ∈ cos '' Icc 1 2` comes from the intermediate value theorem and the lemmas `Real.cos_one_pos` and `Real.cos_two_neg`. The definition does not use uniqueness: every property of `π` follows from the facts that the chosen point lies in `[1, 2]` and that `cos` vanishes there. The notation `π` needs `open Real`. The first bounds are `Real.pi_pos`, `Real.one_le_pi_div_two` and `Real.pi_div_two_le_two`.

<?decl Real.pi?>
:::

### Theorems and proofs

**Theorem (Pythagoras and the addition formulas).** For all $z, w \in \mathbb{C}$, $\sin^2 z + \cos^2 z = 1$ and
$$\cos(z + w) = \cos z \cos w - \sin z \sin w, \qquad \sin(z + w) = \sin z \cos w + \cos z \sin w.$$
For real $x$, $|\sin x| \le 1$ and $|\cos x| \le 1$.

*Proof.* Write $u = e^{iz}$, $v = e^{iw}$. Then $e^{-iz} = u^{-1}$, because $e^{iz}e^{-iz} = e^0 = 1$. Since $(2i)^2 = -4$,
$$\cos^2 z + \sin^2 z = \frac{(u + u^{-1})^2 - (u - u^{-1})^2}{4} = \frac{4uu^{-1}}{4} = 1.$$
Next, $e^{i(z+w)} = uv$, so $\cos(z + w) = (uv + u^{-1}v^{-1})/2$. On the right side,
$$\frac{(u + u^{-1})(v + v^{-1}) + (u - u^{-1})(v - v^{-1})}{4} = \frac{2uv + 2u^{-1}v^{-1}}{4},$$
because the mixed terms $uv^{-1}$ and $u^{-1}v$ cancel. For the sine the right side is $\frac{(u - u^{-1})(v + v^{-1}) + (u + u^{-1})(v - v^{-1})}{4i} = \frac{2uv - 2u^{-1}v^{-1}}{4i} = \sin(z + w)$. For real $x$ both values are real, so $\sin^2 x \le 1$ and $\cos^2 x \le 1$. $\square$

In Mathlib these are `Real.sin_sq_add_cos_sq`, `Real.sin_add` and `Real.cos_add`, in the module of `Real.sin`.

**Lemma (Estimates near zero).** For real $x$ with $|x| \le 1$,
$$\left| \cos x - \Bigl(1 - \frac{x^2}{2}\Bigr) \right| \le \frac{5}{96} |x|^4, \qquad \left| \sin x - \Bigl(x - \frac{x^3}{6}\Bigr) \right| \le \frac{|x|^5}{100}.$$

*Proof.* The first difference is the tail $\sum_{k \ge 2} (-1)^k x^{2k}/(2k)!$, at most $\sum_{m \ge 4} |x|^m/m!$ in absolute value. For $m \ge 4$, $m! \ge 24 \cdot 5^{m-4}$, and $|x|^m \le |x|^4$. So the tail is at most $\frac{|x|^4}{24}\sum_{j \ge 0} 5^{-j} = \frac{5}{96}|x|^4$. For the sine, $m! \ge 120 \cdot 6^{m-5}$ for $m \ge 5$, and the tail is at most $\frac{|x|^5}{120} \cdot \frac65 = \frac{|x|^5}{100}$. $\square$

::: mathlib
`Real.cos_bound` · `Mathlib.Analysis.Complex.Trigonometric`

The first estimate, with the same constant `5 / 96`. The second is `Real.sin_bound`. Both come from the tail bound `Complex.exp_bound`.

<?decl Real.cos_bound?>
:::

**Theorem (A zero of cosine).** $\cos 1 > 0$ and $\cos 2 < 0$. The function $\sin$ is positive on $(0, 2]$, and $\cos$ is strictly decreasing on $[0, 2]$. So $\cos$ has exactly one zero in $[1, 2]$.

*Proof.* By the lemma, $\frac{43}{96} \le \cos 1 \le \frac{53}{96}$. By the double angle formula, $\cos 2 = 2\cos^2 1 - 1 \le 2\bigl(\frac{53}{96}\bigr)^2 - 1 = \frac{5618}{9216} - 1 < 0$. For $0 < y \le 1$ the lemma gives $\sin y \ge y\bigl(1 - \frac16 - \frac1{100}\bigr) > 0$ and $\cos y \ge 1 - \frac12 - \frac5{96} > 0$. For $0 < x \le 2$ put $y = x/2$: then $\sin x = 2\sin y\cos y > 0$. The derivative of $\cos$ is $-\sin$, by the theorem (Derivatives) below, whose proof uses only the lemma and the addition formula. So $\cos' < 0$ on $(0, 2]$, and by the mean value theorem of Chapter 3, $\cos$ is strictly decreasing on $[0, 2]$. The intermediate value theorem of Chapter 2 gives a zero in $(1, 2)$, and a strictly decreasing function has at most one zero. $\square$

So $\cos(\pi/2) = 0$ and $2 < \pi < 4$. Since $\cos$ decreases from $1$ to $0$ on $[0, \pi/2]$ and is even, $\cos x > 0$ for $|x| < \pi/2$. Also $\sin(\pi/2) > 0$ and $\sin^2(\pi/2) = 1$, so $\sin(\pi/2) = 1$.

**Theorem (Periodicity).** For all real $x$:
1. $\sin(x + \pi/2) = \cos x$ and $\cos(x + \pi/2) = -\sin x$;
2. $\sin(x + \pi) = -\sin x$ and $\cos(x + \pi) = -\cos x$;
3. $\sin(x + 2\pi) = \sin x$ and $\cos(x + 2\pi) = \cos x$.
Also $\sin \pi = 0$, $\cos \pi = -1$, and $\sin(\pi - x) = \sin x$.

*Proof.* Part 1 is the addition formula with $\cos(\pi/2) = 0$ and $\sin(\pi/2) = 1$. Part 1 applied twice gives part 2: $\sin(x + \pi) = \cos(x + \pi/2) = -\sin x$ and $\cos(x + \pi) = -\sin(x + \pi/2) = -\cos x$. Part 2 applied twice gives part 3. With $x = 0$, part 2 gives $\sin \pi = 0$ and $\cos \pi = -1$. Part 2 with $-x$ gives $\sin(\pi - x) = -\sin(-x) = \sin x$. $\square$

::: mathlib
`Real.sin_periodic` · `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`

`Function.Periodic sin (2 * π)`, which unfolds to `∀ x, sin (x + 2 * π) = sin x`. The half period is `Real.sin_antiperiodic : Function.Antiperiodic sin π`. The general API then gives `Function.Periodic.int_mul` for integer multiples with no new proof. The cosine has `Real.cos_periodic` and `Real.cos_antiperiodic`.

<?decl Real.sin_periodic?>
:::

**Theorem (Zeros of the sine).** $\sin x > 0$ for $0 < x < \pi$. For real $x$, $\sin x = 0$ if and only if $x = n\pi$ for some $n \in \mathbb{Z}$, and $\cos x = 1$ if and only if $x = 2n\pi$ for some $n \in \mathbb{Z}$.

*Proof.* Step 1. For $0 < x \le \pi/2$, $x \in (0, 2]$, so $\sin x > 0$. For $\pi/2 < x < \pi$, $\sin x = \sin(\pi - x) > 0$ with $\pi - x \in (0, \pi/2)$.

Step 2. By $\sin(x + \pi) = -\sin x$ and induction, $\sin(n\pi) = (-1)^n \sin 0 = 0$ for $n \ge 0$, and $\sin(-n\pi) = -\sin(n\pi) = 0$.

Step 3. Let $\sin x = 0$. Put $n = \lfloor x/\pi \rfloor$ and $r = x - n\pi \in [0, \pi)$. By the same induction, $\sin x = (-1)^n \sin r$, so $\sin r = 0$. By step 1, $r = 0$, and $x = n\pi$.

Step 4. If $x = 2n\pi$, then $\cos x = 1$ by periodicity. If $\cos x = 1$, then $\sin^2 x = 0$, so $x = m\pi$, and $\cos(m\pi) = (-1)^m = 1$ forces $m$ even. $\square$

::: mathlib
`Real.sin_eq_zero_iff` · `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`

`sin x = 0 ↔ ∃ n : ℤ, (n : ℝ) * π = x`. The proof in Mathlib is the proof above, with the floor of `x / π` and `Real.sin_pos_of_pos_of_lt_pi`, whose two hypotheses `0 < x` and `x < π` are separate. The cosine version is `Real.cos_eq_one_iff`.

<?decl Real.sin_eq_zero_iff?>
:::

**Theorem (Derivatives).** $\displaystyle\lim_{h \to 0} \frac{\sin h}{h} = 1$ and $\displaystyle\lim_{h \to 0} \frac{\cos h - 1}{h} = 0$. The functions $\sin$ and $\cos$ are differentiable on $\mathbb{R}$, with $\sin' = \cos$ and $\cos' = -\sin$.

*Proof.* For $0 < |h| \le 1$ the lemma gives
$$\left| \frac{\sin h}{h} - 1 \right| \le \frac{h^2}{6} + \frac{h^4}{100}, \qquad \left| \frac{\cos h - 1}{h} \right| \le \frac{|h|}{2} + \frac{5}{96}|h|^3.$$
The right sides tend to $0$. By the addition formula,
$$\frac{\sin(x + h) - \sin x}{h} = \sin x \cdot \frac{\cos h - 1}{h} + \cos x \cdot \frac{\sin h}{h} \to \cos x,$$
$$\frac{\cos(x + h) - \cos x}{h} = \cos x \cdot \frac{\cos h - 1}{h} - \sin x \cdot \frac{\sin h}{h} \to -\sin x. \qquad \square$$

::: mathlib
`Real.hasDerivAt_sin` · `Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv`

`HasDerivAt sin (cos x) x`, the real part of `Complex.hasDerivAt_sin`. The chain rule form is `HasDerivAt.sin`, and `Real.deriv_sin : deriv sin = cos` is a simp lemma. The cosine is `Real.hasDerivAt_cos`. The limit of $\sin x/x$ is `Real.tendsto_sin_div_nhdsNE_zero`, on the punctured filter `𝓝[≠] 0` of Volume 13, because `sin 0 / 0` is the junk value `0`.

<?decl Real.hasDerivAt_sin?>
:::

**Corollary (Monotonicity).** $\cos$ is strictly decreasing on $[0, \pi]$, and $\sin$ is strictly increasing on $[-\pi/2, \pi/2]$.

*Proof.* On $(0, \pi)$, $\cos' = -\sin < 0$. On $(-\pi/2, \pi/2)$, $\sin' = \cos > 0$. Apply the monotonicity criterion of Chapter 3. $\square$

In Mathlib this is `Real.strictAntiOn_cos` on `Icc 0 π` and `Real.strictMonoOn_sin`.

### Examples

**Example (Values at the special angles).** Put $y = \pi/4$. By part 1 of the periodicity theorem, $\sin(\pi/4) = \cos(\pi/2 - \pi/4) = \cos(\pi/4)$, and both are positive. By Pythagoras, $2\cos^2(\pi/4) = 1$, so $\cos(\pi/4) = \sqrt2/2$. Next put $t = \pi/6$. The addition formulas give $\sin 3t = 3\sin t - 4\sin^3 t$, and $\sin 3t = \sin(\pi/2) = 1$. So $s = \sin t$ solves $4s^3 - 3s + 1 = 0$, that is $(s + 1)(2s - 1)^2 = 0$. Since $s > 0$, $\sin(\pi/6) = 1/2$. Mathlib has `Real.cos_pi_div_four` and `Real.sin_pi_div_six`.

**Counterexample (Periodicity needs a full period).** The number $\pi$ is a period of $|\sin|$ but not of $\sin$: $\sin(3\pi/2) = -1 \ne 1 = \sin(\pi/2)$. No $p \in (0, 2\pi)$ is a period of $\sin$. If $\sin(x + p) = \sin x$ for all $x$, then $x = 0$ gives $\sin p = 0$, so $p = \pi$, which fails. So $2\pi$ is the least positive period.

### The library around it

The file `Trigonometric.Basic` has the definition of `π` and long lists of values and signs, with regular names: values `Real.sin_pi`, `Real.cos_pi_div_two`; shifts `Real.sin_add_pi`, `Real.sin_add_two_pi`, `Real.cos_pi_div_two_sub`; signs `Real.sin_nonneg_of_nonneg_of_le_pi`, `Real.cos_pos_of_mem_Ioo`; injectivity `Real.injOn_cos`. The file `Trigonometric.Deriv` has the `HasDerivAt`, `deriv` and `ContDiff` forms for `sin`, `cos`, `sinh` and `cosh`.

Common errors of a learner:

- The angle in Mathlib is a real number in radians. The value $\sin 30$ in Lean is the sine of $30$ radians.
- `Real.sin` and `Complex.sin` are different functions. A goal about `Complex.sin (x : ℂ)` needs `Complex.ofReal_sin`, often through `push_cast`.
- `π` is defined by choice and does not compute. A goal such as `π < 4` needs a lemma, for example `Real.pi_lt_four`, not `norm_num` alone.
- `Real.sin_eq_zero_iff` gives an integer `n`. A proof that wants a natural number must treat the negative case.

### Exercises

1. (A) Prove $\cos 2x = 1 - 2\sin^2 x$ from the addition formula and Pythagoras.
2. (A) Prove that $\sin 1 > 0.82$ with the lemma. Hint: $1 - 1/6 - 1/100$.
3. (B) Prove that $\cos x = 0$ if and only if $x = (2k + 1)\pi/2$ for some $k \in \mathbb{Z}$. Hint: $\cos x = \sin(x + \pi/2)$.
4. (B) Prove $1 - x^2/2 \le \cos x$ for all real $x$. Hint: first prove $\sin x \le x$ for $x \ge 0$ by a derivative, then study $g(x) = \cos x - 1 + x^2/2$ on $[0, \infty)$ and use evenness.
5. (B) Let $f$ be twice differentiable with $f'' = -f$, $f(0) = 0$, $f'(0) = 1$. Prove $f = \sin$. Hint: for $g = f - \sin$, the function $g^2 + (g')^2$ has derivative $0$.
6. (C) Show that $t \mapsto (\cos t, \sin t)$ is a bijection from $[0, 2\pi)$ onto the unit circle. Hint: for $b \ge 0$ find $t \in [0, \pi]$ with $\cos t = a$ by the intermediate value theorem, and use the monotonicity of $\cos$.

### Notes and history

The series for sine and cosine appear in the work of Madhava in the fourteenth century and in Newton (1669). Euler's *Introductio* (1748) gave $e^{ix} = \cos x + i\sin x$. The definition of $\pi$ by the first zero of cosine is in Rudin, *Principles of Mathematical Analysis*, Section 8.7. In Mathlib the file was ported from Lean 3, where Chris Hughes wrote the first version.

### Reference

<?reference?>
