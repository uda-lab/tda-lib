import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The real line as a topological space

`realLine` is `ℝ` with its ordinary topology as an object of `TopCat.{0}`. It is the base space
shared by the sheaf modules on the real line (`BandConvolution`, `RealStratification`); keeping one
definition lets their constructions compose.
-/

set_option autoImplicit false

namespace TDA.Sheaf

/-- The real line with its ordinary topology, as an object of `TopCat.{0}`. -/
abbrev realLine : TopCat.{0} := TopCat.of ℝ

end TDA.Sheaf
