# One endpoint role per face

Fix a face-compatible enumeration of a finite complex and a coefficient field.
At step `i + 1`, the actual prefix inclusion adds exactly the face at index `i`.
For each homological degree, the canonical rank barcode counts births by the
cokernel dimension and deaths by the kernel dimension of this adjacent inclusion.
This follows by subtracting the adjacent rank from the target and source ranks,
respectively. It uses the rank barcode's interval rank count, not an interval
decomposition of the actual homology module.

The actual attachment theorem classifies the new face: an isolated vertex gives
one degree-zero birth; a higher simplex gives either one birth in its own degree
or one death in the degree below. All other inclusion maps are bijective. Thus
exactly one birth or death count is one across *all* degrees, and every other
count is zero.

The finite pair template shifts birth and finite death stages down by one to
face indices. Essential intervals contribute only their birth index. The terminal
death at `m + 1` has no face index. Consequently the total multiplicity of
finite first endpoints, finite second endpoints, and essential birth indices at
each face is exactly one. In particular finite pairs and essential indices have
multiplicity at most one, and endpoint roles in different degrees cannot overlap.

Examples: the empty complex has no endpoint to classify. The sole vertex of a
one-face complex is an essential degree-zero birth. An edge joining components
is a degree-zero death. A cycle-closing edge is a degree-one birth, and a triangle
filling that cycle is a degree-one death. Equal filtration values can still give
repeated evaluated diagram points; this is an index statement, and `Q` may remove
zero-length evaluated pairs.

The degree-specific lemmas for finite deaths and births feed the face-count argument in
[total persistence and finite Rips–Čech bounds](total-persistence.md).
