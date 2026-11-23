import TDA.Filtration.CollapseCertificateFamily
import TDA.Persistence.CollapsePersistence

set_option autoImplicit false

/-!
# Persistence isomorphisms from accepted certificate families

Let `F` and `G` be real-indexed simplicial filtrations with `F t ≤ G t` at every grade and with
rational grade tables `gF` and `gG` (`HasGradeTable`). If `checkCertificates gF gG cert`
accepts a supplied certificate family, then `G t` collapses to `F t` at every real grade
(`collapsesTo_of_checkCertificates`), so the inclusion morphism `inclusionHom R n hle` of their
homology persistence modules is an isomorphism, in every degree `n` and over every ring `R`
(`isIso_inclusionHom_of_checkCertificates`). `certificateInclusionIso` packages it; its
forward map is `inclusionHom R n hle`, whose components are the homology maps of the actual
inclusions, so naturality is the functoriality of those inclusions and the retractions of the
collapses at different grades are never compared.

The certificates are supplied. These are library derivations; no source theorem is attributed
to them.
-/

universe u v

namespace TDA.Persistence

open CategoryTheory TDA.Simplicial TDA.Filtration

variable {V : Type u} [LinearOrder V]
variable (R : Type v) [Ring R] (n : ℕ)
variable {F G : SimplicialFiltration ℝ V} {gF gG : Finset (Finset V × ℚ)}
  {cert : ℚ → List (Finset V × Finset V)}

/-- If a certificate family for the grade tables of `F` and `G` is accepted, the inclusion
morphism of homology persistence modules is an isomorphism, in every degree and over every
ring. -/
theorem isIso_inclusionHom_of_checkCertificates (hle : ∀ t, F t ≤ G t)
    (hF : HasGradeTable F gF) (hG : HasGradeTable G gG)
    (h : checkCertificates gF gG cert = true) : IsIso (inclusionHom R n hle) :=
  isIso_inclusionHom_of_collapsesTo R n hle (collapsesTo_of_checkCertificates hF hG h)

/-- The natural isomorphism of homology persistence modules induced by the inclusions, when a
certificate family for the grade tables of `F` and `G` is accepted. -/
noncomputable def certificateInclusionIso (hle : ∀ t, F t ≤ G t) (hF : HasGradeTable F gF)
    (hG : HasGradeTable G gG) (h : checkCertificates gF gG cert = true) :
    simplicialHomologyPModule R F n ≅ simplicialHomologyPModule R G n :=
  collapseInclusionIso R n hle (collapsesTo_of_checkCertificates hF hG h)

/-- The forward map of `certificateInclusionIso` is the inclusion morphism. -/
@[simp] theorem certificateInclusionIso_hom (hle : ∀ t, F t ≤ G t) (hF : HasGradeTable F gF)
    (hG : HasGradeTable G gG) (h : checkCertificates gF gG cert = true) :
    (certificateInclusionIso R n hle hF hG h).hom = inclusionHom R n hle := rfl

end TDA.Persistence
