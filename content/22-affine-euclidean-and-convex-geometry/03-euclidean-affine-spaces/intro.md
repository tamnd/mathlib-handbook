# Euclidean affine spaces

Chapters 1 and 2 studied affine spaces, which do not know length or angle. This chapter adds an inner product on the space of vectors and studies the geometry that it gives: the Euclidean geometry of Euclid's *Elements*, in each dimension.

Section 1 defines the distance and the angle at a point, with values in $[0, \pi]$. It shows that the angles $0$ and $\pi$ are the cases of betweenness, that isometries keep angles, and that angles satisfy a triangle inequality. Section 2 proves the classical theorems on triangles: the law of cosines, Pythagoras and its converse, the isosceles triangle, the angle sum $\pi$, the law of sines and the congruence criteria. Section 3 builds the orthogonal projection onto an affine subspace, the reflection in it, the perpendicular bisector of two points and the signed distance.

In Mathlib these results are in `Mathlib.Geometry.Euclidean` and its folder `Angle.Unoriented`. Chapter 4 refines the angle in the plane to an oriented angle, and Chapter 5 uses all of these tools for spheres and the centres of a triangle.
