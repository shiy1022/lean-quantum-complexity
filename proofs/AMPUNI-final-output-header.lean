import «AMPUNI-complete-controller-forward-output»
import Theorems.Thm_ShiClassQMAAmpX_ampFamilyX_resource_identities_and_regularity

set_option autoImplicit false

open ShiClassQMAAmpX

namespace ShiTMCompleteController

/-- The already-emitted numeric fields are exactly the amplified verifier's
three numeric fields. The remaining output obligation concerns only the
circuit field. -/
theorem amplified_family_encoding_header
    (F : ShiClassQMA.QMAFamily) (n : Nat) :
    ShiClassQMAU.encQMAFamilyAt (ampFamilyX F) n =
      ShiBQP.encNat (3 * F.wit n) ++
      ShiBQP.encNat (2 * n + 3 * F.anc n + 3) ++
      ShiBQP.encNat (3 * n + 3 * F.wit n + 3 * F.anc n + 3) ++
      ShiBQP.encCirc (ampCircX F n) := by
  have hw := ampFamilyX_resource_identities_and_regularity.1 F n
  have ha := ampFamilyX_resource_identities_and_regularity.2.1 F n
  have ho := ampFamilyX_resource_identities_and_regularity.2.2.1 F n
  unfold ShiClassQMAU.encQMAFamilyAt
  simp only [hw, ha, ho]
  rfl

end ShiTMCompleteController
