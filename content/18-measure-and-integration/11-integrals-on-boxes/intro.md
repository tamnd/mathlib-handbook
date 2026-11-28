# Integrals on boxes

This chapter studies integrals that are limits of Riemann sums over partitions of a box in $\mathbb{R}^n$. Mathlib defines the integrals of Riemann, of Henstock and Kurzweil and of McShane with one definition, in the namespace `BoxIntegral`. The definition takes a filter on tagged partitions, and three Boolean parameters select the filter.

Section 1 defines boxes, prepartitions, partitions and tagged prepartitions. It proves that every gauge has a subordinate tagged partition, defines box additive maps such as the volume and counts lattice points in a domain with partitions into small cubes. Section 2 defines the integration parameters, the filters and the integral. It proves the rules of computation and the criteria of integrability, identifies the integral of McShane with the Bochner integral and proves the divergence theorem on a box.

The chapter needs the topology of Volume 13, the measures of Chapter 2 and the Bochner integral of Chapter 5. The divergence theorem of Chapter 8 rests on the results of Section 2.
