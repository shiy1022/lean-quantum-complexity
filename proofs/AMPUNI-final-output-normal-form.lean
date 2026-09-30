import «AMPUNI-final-output-header»
import «AMPUNI-circuit-normalization-spec»
import «AMPUNI-concrete-copy-alignment»

set_option autoImplicit false

open ShiShallow ShiClassQMAAmpX

namespace ShiTMCompleteController

/-- Exact final-string specification: the amplified family's circuit field has
one depth prefix, then the payloads of two fixed fanout blocks, three verifier
copies, and the fixed majority-readout block. -/
theorem amplified_encoding_six_payloads
    (F : ShiClassQMA.QMAFamily) (n : Nat) :
    ∃ (c₁ c₂ c₃ :
        Layered (n + (3 * F.wit n + ((2 * n + 3 * F.anc n + 3) + 1)))),
      ampCircX F n =
        ampFan2X n (F.wit n) (F.anc n) ++
        ampFan3X n (F.wit n) (F.anc n) ++
        c₁ ++ c₂ ++ c₃ ++
        ampReadX n (F.wit n) (F.anc n) (F.out n)
      ∧ ShiClassQMAU.encQMAFamilyAt (ampFamilyX F) n =
          ShiBQP.encNat (3 * F.wit n) ++
          ShiBQP.encNat (2 * n + 3 * F.anc n + 3) ++
          ShiBQP.encNat (3 * n + 3 * F.wit n + 3 * F.anc n + 3) ++
          ShiBQP.encNat
            ((ampFan2X n (F.wit n) (F.anc n)).length +
              (ampFan3X n (F.wit n) (F.anc n)).length +
              c₁.length + c₂.length + c₃.length +
              (ampReadX n (F.wit n) (F.anc n) (F.out n)).length) ++
          ShiTMCircuitNormalization.stripCircPrefix
            (ampFan2X n (F.wit n) (F.anc n)) ++
          ShiTMCircuitNormalization.stripCircPrefix
            (ampFan3X n (F.wit n) (F.anc n)) ++
          ShiTMCircuitNormalization.stripCircPrefix c₁ ++
          ShiTMCircuitNormalization.stripCircPrefix c₂ ++
          ShiTMCircuitNormalization.stripCircPrefix c₃ ++
          ShiTMCircuitNormalization.stripCircPrefix
            (ampReadX n (F.wit n) (F.anc n) (F.out n)) := by
  refine ⟨embeddedCopy0 F n, embeddedCopy1 F n,
    embeddedCopy2 F n, ampCircX_exact_copies F n, ?_⟩
  rw [amplified_family_encoding_header, ampCircX_exact_copies,
    ShiTMCircuitNormalization.six_block_normalization]
  simp only [List.append_assoc]

end ShiTMCompleteController
