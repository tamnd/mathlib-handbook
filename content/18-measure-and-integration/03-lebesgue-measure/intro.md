# Lebesgue measure

Chapter 2 gave the general theory of measures and the Carathéodory construction. This chapter applies it to the measure that the rest of the volume uses most: Lebesgue measure on the real line and on $\mathbb{R}^n$.

Section 1 builds Lebesgue measure on $\mathbb{R}$ as a Lebesgue-Stieltjes measure. A monotone right continuous function $f$ gives the length $f(b) - f(a)$ to the interval $(a, b]$, the Carathéodory construction extends it to an outer measure, and the Borel sets are measurable for it. The identity function gives Lebesgue measure. The section proves that the measure is translation invariant and outer regular, and it shows how Mathlib identifies its `volume` on `ℝ` with the Stieltjes measure of the identity.

Section 2 goes to $\mathbb{R}^n$. It proves that Lebesgue measure is the only translation invariant measure that is finite on compact sets, up to a constant factor, and that a linear map $T$ multiplies it by $|\det T|$. This is the theorem of Haar for the group $\mathbb{R}^n$, and Mathlib defines the volume of a finite dimensional inner product space as a Haar measure. The section ends with the Vitali set, which shows that not every subset of $\mathbb{R}$ is measurable.

The chapter uses the topology of $\mathbb{R}^n$ from Volume 13, the determinant from Volume 7 and the real line of Volume 15. Product measures, which give a second construction of Lebesgue measure on $\mathbb{R}^n$, come in Chapter 6.
