import TDA.Persistence.CollapseCertificatePersistence
import TDA.Persistence.CollapsePersistenceExamples
import TDA.Filtration.AlphaCollapseFamilyExamples

set_option autoImplicit false

/-!
# The obtuse triangle's persistence isomorphism through the certificate verifier

On `RationalAlpha.Examples.obtuse`, the accepted family `obtuseCertificate` and the grade tables
of the actual squared-grade Čech and α filtrations give, through the generic verifier, the
natural isomorphism from α persistence to squared-grade Čech persistence induced by the labelled
inclusions, in every degree and over every ring (`isIso_inclusionHom_of_certificate`,
`alphaCechCertificateIso`). It is the isomorphism `CollapsePersistenceExamples.alphaCechIso`
obtained from the hand proof of the collapses (`alphaCechCertificateIso_eq`): both have forward
map the inclusion morphism, and only the proof of the collapses differs.
-/

namespace TDA.Persistence.CollapseCertificatePersistenceExamples

open CategoryTheory TDA.Simplicial TDA.Filtration TDA.Filtration.RationalAlpha
open TDA.Filtration.RationalAlpha.Examples TDA.Filtration.AlphaCollapseFamilyExamples

/-- Through the verifier, the labelled inclusions induce an isomorphism of homology persistence
modules, in every degree and over every ring. -/
theorem isIso_inclusionHom_of_certificate (R : Type*) [Ring R] (n : ℕ) :
    IsIso (inclusionHom R n (Alpha.labelledComplexFiltration_le_squaredCech (realSites obtuse))) :=
  isIso_inclusionHom_of_checkCertificates R n _ hasGradeTable_alpha hasGradeTable_cech
    checkCertificates_obtuse

/-- The natural isomorphism from α persistence to squared-grade Čech persistence of the obtuse
triangle, obtained through the certificate verifier. -/
noncomputable def alphaCechCertificateIso (R : Type*) [Ring R] (n : ℕ) :
    simplicialHomologyPModule R (Alpha.labelledComplexFiltration (realSites obtuse)) n ≅
      simplicialHomologyPModule R (Alpha.squaredCechFiltration (realSites obtuse)) n :=
  certificateInclusionIso R n (Alpha.labelledComplexFiltration_le_squaredCech (realSites obtuse))
    hasGradeTable_alpha hasGradeTable_cech checkCertificates_obtuse

/-- The forward map of `alphaCechCertificateIso` is the inclusion morphism. -/
theorem alphaCechCertificateIso_hom (R : Type*) [Ring R] (n : ℕ) :
    (alphaCechCertificateIso R n).hom =
      inclusionHom R n (Alpha.labelledComplexFiltration_le_squaredCech (realSites obtuse)) :=
  rfl

/-- The isomorphism obtained through the verifier is `CollapsePersistenceExamples.alphaCechIso`. -/
theorem alphaCechCertificateIso_eq (R : Type*) [Ring R] (n : ℕ) :
    alphaCechCertificateIso R n = CollapsePersistenceExamples.alphaCechIso R n :=
  Iso.ext rfl

end TDA.Persistence.CollapseCertificatePersistenceExamples
