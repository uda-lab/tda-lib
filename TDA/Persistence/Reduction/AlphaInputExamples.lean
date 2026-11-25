import TDA.Filtration.RationalAlphaExamples
import TDA.Persistence.Reduction.AlphaInput

/-! Executed point-cloud-to-barcode fixtures for the exact α runner. -/

set_option autoImplicit false

namespace TDA.Persistence.Reduction.AlphaInput.Examples

open TDA.Filtration

#eval show IO Unit from do
  let some bars := run RationalAlpha.Examples.square
    | throw (IO.userError "square was rejected")
  unless bars.filter (·.degree == 1) == [⟨1, 1, .finite 2⟩] do
    throw (IO.userError s!"unexpected square H₁ barcode {repr bars}")
  unless bars.filter (·.degree == 0) ==
      [⟨0, 0, .finite 1⟩, ⟨0, 0, .finite 1⟩, ⟨0, 0, .finite 1⟩, ⟨0, 0, .essential⟩] do
    throw (IO.userError s!"unexpected square H₀ barcode {repr bars}")

#eval show IO Unit from do
  let some bars := run RationalAlpha.Examples.obtuse
    | throw (IO.userError "obtuse triangle was rejected")
  unless bars.filter (·.degree == 1) == [] do
    throw (IO.userError s!"unexpected obtuse triangle H₁ barcode {repr bars}")
  unless bars.filter (·.degree == 0) ==
      [⟨0, 0, .finite (1/2)⟩, ⟨0, 0, .finite (5/2)⟩, ⟨0, 0, .essential⟩] do
    throw (IO.userError s!"unexpected obtuse triangle H₀ barcode {repr bars}")

example : run (Fin.elim0 : Fin 0 → RationalAlpha.Point) = some [] := by decide +kernel

example : run (fun _ : Fin 2 => (0,0)) = none := by decide +kernel

end TDA.Persistence.Reduction.AlphaInput.Examples
