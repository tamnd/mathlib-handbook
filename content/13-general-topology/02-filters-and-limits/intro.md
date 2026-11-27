# Filters and limits

Classical analysis has many kinds of limit. A sequence has a limit as $n \to \infty$. A function has a limit as $x \to a$, as $x \to a^{+}$, as $x \to \infty$. Each kind has its own $\varepsilon$-$N$ or $\varepsilon$-$\delta$ definition, and each theorem on limits is proved again for each kind. Mathlib removes this repetition with filters. A filter on a type is a family of subsets that are "large". Each kind of limit is the statement that a map sends large sets of one filter into large sets of another filter.

Section 1 defines filters, the order on filters, the principal filters, the filters `atTop` and `cofinite`, and the words "eventually" and "frequently". It also defines the image and the preimage of a filter under a map, and a basis of a filter. Section 2 defines the neighbourhood filter `𝓝 x` and the predicate `Tendsto`. It translates the limit of a sequence, the limit of a function and continuity into this language, and proves the translations. Section 3 defines cluster points and ultrafilters. It characterises the closure with filters, and shows that in a first countable space sequences are enough, while in general they are not.

The chapter needs Chapter 1 and the complete lattices of Volume 4. The reader who knows the $\varepsilon$-$\delta$ definitions should read Section 2 slowly. Each later chapter uses its language.
