import «AMPUNI-controller-exact-three-copy-output»
import «AMPUNI-final-output-normal-form»

set_option autoImplicit false

open ShiShallow ShiClassQMAAmpX

namespace ShiTMCompleteController

/-- The precise normalization target for the verified three-copy controller:
one global circuit-depth header, fixed fanout/readout payloads, and the three
copy payloads with their local depth headers stripped. -/
theorem amplified_encoding_exact_output_contract
    (F : ShiClassQMA.QMAFamily) (n : Nat) :
    ShiClassQMAU.encQMAFamilyAt (ampFamilyX F) n =
      ShiBQP.encNat (3 * F.wit n) ++
      ShiBQP.encNat (2 * n + 3 * F.anc n + 3) ++
      ShiBQP.encNat (3 * n + 3 * F.wit n + 3 * F.anc n + 3) ++
      ShiBQP.encNat (3 * depth (F.circ n) + 113) ++
      ShiTMCircuitNormalization.stripCircPrefix
        (ampFan2X n (F.wit n) (F.anc n)) ++
      ShiTMCircuitNormalization.stripCircPrefix
        (ampFan3X n (F.wit n) (F.anc n)) ++
      ShiTMCircuitNormalization.stripCircPrefix (embeddedCopy0 F n) ++
      ShiTMCircuitNormalization.stripCircPrefix (embeddedCopy1 F n) ++
      ShiTMCircuitNormalization.stripCircPrefix (embeddedCopy2 F n) ++
      ShiTMCircuitNormalization.stripCircPrefix
        (ampReadX n (F.wit n) (F.anc n) (F.out n)) := by
  have hdepth :=
    ampFamilyX_resource_identities_and_regularity.2.2.2.1 F n
  change (ampCircX F n).length = 3 * depth (F.circ n) + 113 at hdepth
  rw [ampCircX_exact_copies] at hdepth
  simp only [List.length_append] at hdepth
  rw [amplified_family_encoding_header, ampCircX_exact_copies,
    ShiTMCircuitNormalization.six_block_normalization]
  rw [hdepth]
  simp only [List.append_assoc]

end ShiTMCompleteController
