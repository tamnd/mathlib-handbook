# Kernels and stochastic processes

A kernel is a measurable family of measures. It describes one step of a random system, the conditional law of one variable given another, and the transition of a Markov chain. Mathlib uses kernels as the base of much of its probability theory: independence, conditional distributions and the construction of processes all go through them.

Section 1 defines kernels and Markov kernels, their composition and composition-product, and invariant measures. Section 2 disintegrates a measure on a product into a marginal and a conditional kernel, and defines conditional distributions and posteriors. Section 3 builds processes in discrete time with the Ionescu-Tulcea theorem, and defines Gaussian processes, independent increments and Brownian motion.

The chapter needs Chapters 1 to 7 and Volume 18, Measure and integration. In Mathlib, the files are in `Mathlib/Probability/Kernel/`, `Mathlib/Probability/Process/` and `Mathlib/Probability/BrownianMotion/`.
