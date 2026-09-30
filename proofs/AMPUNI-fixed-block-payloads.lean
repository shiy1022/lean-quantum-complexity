import «AMPUNI-exact-output-contract»
import «AMPUNI-explicit-block-encoding»

set_option autoImplicit false

open ShiShallow ShiClassQMAAmp ShiClassQMAAmpX

namespace ShiTMCircuitNormalization

/-- The fanout payload is one layer header followed by exactly `n` encoded
CNOTs at the supplied embedded wire indices. -/
theorem fanEmbCirc_payload (n N : Nat) (g : Fin (n + n) → Fin N)
    (hg : Function.Injective g) :
    stripCircPrefix (fanEmbCirc n N g hg) =
      ShiBQP.encNat n ++
        ((List.finRange n).map (fun j =>
          ShiBQP.encNat 4 ++
          ShiBQP.encNat ((g (Fin.castAdd n j) : Fin N).val) ++
          ShiBQP.encNat ((g (Fin.natAdd n j) : Fin N).val))).flatten := by
  unfold stripCircPrefix
  rw [show (fanEmbCirc n N g hg).length = 1 by rfl,
    ShiTMExplicitBlocks.encCirc_fanEmbCirc]
  simp [ShiBQP.encNat]

theorem ampFan2X_payload (n w a : Nat) :
    stripCircPrefix (ampFan2X n w a) =
      ShiBQP.encNat n ++
        ((List.finRange n).map (fun j =>
          ShiBQP.encNat 4 ++
          ShiBQP.encNat ((ampG2 n w a (Fin.castAdd n j)).val) ++
          ShiBQP.encNat ((ampG2 n w a (Fin.natAdd n j)).val))).flatten := by
  unfold ampFan2X
  exact fanEmbCirc_payload _ _ _ _

theorem ampFan3X_payload (n w a : Nat) :
    stripCircPrefix (ampFan3X n w a) =
      ShiBQP.encNat n ++
        ((List.finRange n).map (fun j =>
          ShiBQP.encNat 4 ++
          ShiBQP.encNat ((ampG3 n w a (Fin.castAdd n j)).val) ++
          ShiBQP.encNat ((ampG3 n w a (Fin.natAdd n j)).val))).flatten := by
  unfold ampFan3X
  exact fanEmbCirc_payload _ _ _ _

/-- The majority readout payload is the fixed three-Toffoli gate template,
one encoded singleton layer per gate. Its outer 111-layer prefix is removed. -/
theorem readCirc_payload {N : Nat}
    (w₁ w₂ w₃ s : Fin N) (h₁₂ : w₁ ≠ w₂) (h₁₃ : w₁ ≠ w₃)
    (h₂₃ : w₂ ≠ w₃) (h₁s : w₁ ≠ s) (h₂s : w₂ ≠ s)
    (h₃s : w₃ ≠ s) :
    stripCircPrefix
        (ShiExplicitCirc.readCirc w₁ w₂ w₃ s h₁₂ h₁₃ h₂₃ h₁s h₂s h₃s) =
      ((ShiExplicitCirc.toffGates w₁ w₂ s h₁₂ h₁s h₂s ++
        ShiExplicitCirc.toffGates w₂ w₃ s h₂₃ h₂s h₃s ++
        ShiExplicitCirc.toffGates w₁ w₃ s h₁₃ h₁s h₃s).map
          (fun g => ShiBQP.encLayer [g])).flatten := by
  rw [stripCircPrefix_eq_payload]
  simp [payload, ShiExplicitCirc.readCirc, ShiExplicitCirc.toffCirc,
    List.map_append, List.flatten_append, List.map_map, List.append_assoc]
  rfl

end ShiTMCircuitNormalization
