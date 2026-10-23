import TDA.Persistence.Basic
import Mathlib.Data.Real.Basic

/-!
# Coordinatewise real index categories

The `TDA.Persistence` scope selects the category induced by coordinatewise order
on real grades. It is shared by rectangle modules and finite presentations.
-/

namespace TDA.Persistence

/-- The coordinatewise preorder category for real grades. Open the
`TDA.Persistence` scope to select this category in multiparameter consumers. -/
scoped instance (priority := 10000) realCoordinatePreorderCategory (n : ℕ) :
    CategoryTheory.SmallCategory (Fin n → ℝ) := Preorder.smallCategory _

end TDA.Persistence
