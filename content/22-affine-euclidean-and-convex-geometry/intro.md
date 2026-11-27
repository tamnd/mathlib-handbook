# Affine, Euclidean and convex geometry

This volume teaches the geometry of affine spaces, the Euclidean geometry of triangles and circles, and the first theorems of convex geometry, together with their form in Mathlib. It starts from an affine space as a set of points with a free and transitive action of a vector space, and it ends with the theorem of Krein-Milman and with convex cones. Each main theorem has a complete proof on paper.

Volume 7 studies vector spaces, where the zero vector is a special point. Geometry has no special point. An affine space keeps the vectors as the differences of points, and it keeps the lines, the planes, the midpoints and the barycentres, but it forgets the origin. A Euclidean affine space adds an inner product on the vectors, from Chapter 6 of Volume 16, and so gets distances and angles. Convex geometry needs only the order of the real numbers: a set is convex if it contains the segment between two of its points. Volume 16 defines convex sets and proves the separation theorem. This volume goes further, to the combinatorial theorems on convex hulls and to extreme points.

The chapters are in the order of a course.

- Chapter 1 defines affine spaces as torsors under a vector space, affine maps and their linear parts, affine equivalences, slopes, and continuous affine maps.
- Chapter 2 studies affine subspaces and their directions, affine spans, affine combinations and centroids, the theorem of Ceva, affine independence, affine bases and barycentric coordinates, simplices, and the betweenness of points and the sides of a hyperplane.
- Chapter 3 defines Euclidean affine spaces and the unoriented angle, proves the theorems on triangles (the law of cosines, the angle sum, the law of sines, the congruence and similarity criteria), and studies orthogonal projections, reflections, perpendicular bisectors and signed distances.
- Chapter 4 defines the orientation of a plane and the oriented angle with values modulo $2\pi$, proves the oriented angle sum, and studies rotations and right-angled triangles.
- Chapter 5 proves the classical theorems on spheres and triangles: the power of a point, tangents, the inscribed angle theorem, Thales, Ptolemy, inversion, Euler's quadrilateral theorem, and the circumcentre, orthocentre, nine-point circle, incentre and area of a triangle.
- Chapter 6 studies convex sets and convex functions in a vector space and in the abstract convex spaces of Mathlib.
- Chapter 7 studies convex hulls, convex combinations and the standard simplex, and proves the theorems of Carathéodory, Radon and Helly.
- Chapter 8 studies extreme and exposed points, proves the theorem of Krein-Milman, and studies convex cones, their duals and faces, simplicial complexes and polygons, and says how far Mathlib goes towards polytopes.

The volume needs Volume 5 for group actions, since an affine space is a torsor, Volume 7 for vector spaces, linear maps, dimension and matrices, Volume 13 for the topology of Chapter 1 and of Chapter 8, Volume 15 for the trigonometric functions and $\arccos$, and Volume 16 for inner product spaces, orthogonal projection, convex sets and the separation theorem. It is the last volume of the undergraduate reading path.

Mathlib states this geometry in more generality than a course. An affine space is a type `P` with an action `+ᵥ` of an additive group `V` and a subtraction `-ᵥ`, and most of Euclidean geometry is stated in any dimension. Results special to the plane ask for the instance `Fact (finrank ℝ V = 2)`. Several constructions have a value at a degenerate input that a textbook leaves undefined, for example the angle with a zero vector is $\pi/2$. The text names these conventions where they matter. The volume has no Lean companion yet, so the sections show the Mathlib statements and give no Lean exercises.
