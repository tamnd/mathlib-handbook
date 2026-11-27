# General topology

This volume teaches general topology and its form in Mathlib. It starts from the axioms of a topological space and ends with the theorems of Urysohn and Tietze. Each main theorem has a complete proof on paper. Each definition has its Mathlib name, the module that contains it, and a note on the choices that the library makes.

The volume has one feature that a reader of a classical text does not expect. Mathlib does not define limits with sequences, and it does not define limits with $\varepsilon$ and $\delta$. It defines them with filters. A filter is a family of sets that are "large" in some sense: the neighbourhoods of a point, the sets that contain all but finitely many natural numbers, the sets that contain a tail $[N, \infty)$. One predicate, `Filter.Tendsto f l₁ l₂`, then says "$f(x)$ is in each large set of $l_2$ when $x$ is in a large set of $l_1$". This one predicate covers the limit of a sequence, the limit of a function at a point, the limit at infinity, the one-sided limits and continuity. Chapter 2 explains filters slowly, for a reader who knows the $\varepsilon$-$\delta$ definitions, and translates each classical form into the filter form and back. The rest of the volume uses filters as its main tool. The proofs of compactness of $[0,1]$ and of the Tychonoff theorem are filter proofs.

The chapters are in the order of a first course.

- Chapter 1 defines topological spaces, open and closed sets, closure and interior, bases and neighbourhoods, continuous maps and homeomorphisms, and the subspace and product topologies. The cofinite topology is the first example that is not a metric space.
- Chapter 2 defines filters, the neighbourhood filter $\mathcal{N}(x)$, written `𝓝 x` in Mathlib, the predicate `Tendsto`, cluster points and ultrafilters. It shows when sequences are enough and when they are not.
- Chapter 3 studies metric spaces: balls, the metric topology, the $\varepsilon$-$\delta$ form of continuity and its filter form, bounded sets, the extended metric spaces of Mathlib, complete metric spaces and the Baire category theorem.
- Chapter 4 studies the separation axioms $T_0$, $T_1$, $T_2$, regular and normal spaces. A limit is unique in a Hausdorff space, and a metric space is normal.
- Chapter 5 studies compactness. It proves that the filter definition of Mathlib agrees with the open cover definition, gives the filter proof that $[0,1]$ is compact, proves the Tychonoff theorem with ultrafilters, and proves the Heine-Borel theorem in metric spaces: compact is equivalent to complete and totally bounded, and to sequentially compact.
- Chapter 6 studies connectedness, the intermediate value theorem, connected components, path connectedness and the topologist's sine curve.
- Chapter 7 studies uniform spaces, Cauchy filters, complete spaces and the completion. It proves the theorem of Heine on uniform continuity, that $\mathbb{Q}$ is not complete, and that its completion is $\mathbb{R}$.
- Chapter 8 proves the lemma of Urysohn and the extension theorem of Tietze for normal spaces.

The volume needs Volume 1 for sets, functions, subtypes and classes, Volume 3 for finite and countable sets, and Volume 4 for orders, lattices, complete lattices and the supremum in $\mathbb{R}$. The filters of a type form a complete lattice, and the topologies on a type form a complete lattice, so Volume 4 is used from the first chapter. Volume 2 gives the real numbers. Read the chapters in order. Chapters 5 and 7 use all the earlier chapters. Volume 14 on topological algebra and infinite sums, and Volume 15 on real analysis, start where this volume stops.

The volume has no companion Lean files yet. The Mathlib boxes give the real names and signatures at the edition commit.
