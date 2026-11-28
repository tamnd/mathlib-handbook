# Metric spaces

A metric space is a set with a distance. The open balls form a basis of a topology, and in this topology the filter statements of Chapter 2 become the $\varepsilon$-$\delta$ statements of analysis. Metric spaces are the main examples of the volume, and most of the spaces of analysis are metric spaces.

Section 1 defines metric spaces and pseudometric spaces, balls, the metric topology and bounded sets. It proves the $\varepsilon$-$\delta$ forms of limits and continuity, and it explains the classes of Mathlib: `PseudoMetricSpace`, `MetricSpace`, the extended forms `EMetricSpace` and `PseudoEMetricSpace`, and the choice of the sup distance on products. Section 2 defines Cauchy sequences and complete metric spaces, and proves the Baire category theorem: in a complete metric space a countable intersection of dense open sets is dense.

Section 3 is a guide to the rest of the pseudometric library: the ways to build metric structures, finite products, proper spaces, Cauchy sequences, completions and bundled pseudometrics. Section 4 treats extended metric spaces, with the extended diameter, paracompactness, the shrinking lemma and the weak extended metrics on $[0, \infty]$. Section 5 treats Lipschitz, antilipschitz and Hölder maps, the extension of Lipschitz real functions and the Hölder norm. Section 6 treats bornologies on products and subtypes, locally bounded maps and absorbing sets.

The chapter needs Chapters 1 and 2, and the real numbers of Volume 2. Chapter 7 puts the completeness of Section 2 in the general frame of uniform spaces.
