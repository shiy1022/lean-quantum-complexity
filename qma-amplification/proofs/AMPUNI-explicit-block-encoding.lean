import Definitions.Def_ShiClassQMAAmpX

set_option autoImplicit false

open ShiShallow ShiClassQMAAmpX

namespace ShiTMExplicitBlocks

private def encGateLayer {N : ℕ} (g : Instr N) : PvsNP.Str :=
  ShiBQP.encNat 1 ++ ShiBQP.encInstr g

theorem encLayer_singleton {N : ℕ} (g : Instr N) :
    ShiBQP.encLayer [g] = encGateLayer g := by
  simp [ShiBQP.encLayer, ShiBQP.encStr, encGateLayer]

/-- Encoding a one-gate-per-layer circuit is just its gate count followed by one fixed layer
header and one instruction encoding per gate. -/
theorem encCirc_singleton_layers {N : ℕ} (gs : List (Instr N)) :
    ShiBQP.encCirc (gs.map (fun g => [g]))
      = ShiBQP.encNat gs.length ++ (gs.map encGateLayer).flatten := by
  simp [ShiBQP.encCirc, ShiBQP.encStr, List.map_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro g hg
  exact encLayer_singleton g

/-- Exact encoding target for an embedded fanout: one layer, containing `n` CNOTs. The two
wire indices remain expressed through `g`; the existing layout emitter computes each value. -/
theorem encCirc_fanEmbCirc (n N : ℕ) (g : Fin (n + n) → Fin N)
    (hg : Function.Injective g) :
    ShiBQP.encCirc (fanEmbCirc n N g hg)
      = ShiBQP.encNat 1 ++ ShiBQP.encNat n
        ++ ((List.finRange n).map (fun j =>
          ShiBQP.encNat 4
            ++ ShiBQP.encNat ((g (Fin.castAdd n j) : Fin N).val)
            ++ ShiBQP.encNat ((g (Fin.natAdd n j) : Fin N).val))).flatten := by
  simp [fanEmbCirc, ShiBQP.encCirc, ShiBQP.encStr,
    ShiBQP.encLayer, List.map_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j hj
  rfl

private theorem toffGates_length {N : ℕ} (p q r : Fin N)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (ShiExplicitCirc.toffGates p q r hpq hpr hqr).length = 37 := by
  rfl

theorem readout_gate_list_length {N : ℕ}
    (w₁ w₂ w₃ s : Fin N) (h₁₂ : w₁ ≠ w₂) (h₁₃ : w₁ ≠ w₃)
    (h₂₃ : w₂ ≠ w₃) (h₁s : w₁ ≠ s) (h₂s : w₂ ≠ s) (h₃s : w₃ ≠ s) :
    (ShiExplicitCirc.toffGates w₁ w₂ s h₁₂ h₁s h₂s
      ++ ShiExplicitCirc.toffGates w₂ w₃ s h₂₃ h₂s h₃s
      ++ ShiExplicitCirc.toffGates w₁ w₃ s h₁₃ h₁s h₃s).length = 111 := by
  simp only [List.length_append, toffGates_length]

/-- Exact encoding target for the majority readout. It is a fixed 111-element gate template;
the only data-dependent work is emitting the four supplied wire indices in its H/T/CNOT
instructions. -/
theorem encCirc_readCirc {N : ℕ}
    (w₁ w₂ w₃ s : Fin N) (h₁₂ : w₁ ≠ w₂) (h₁₃ : w₁ ≠ w₃)
    (h₂₃ : w₂ ≠ w₃) (h₁s : w₁ ≠ s) (h₂s : w₂ ≠ s) (h₃s : w₃ ≠ s) :
    let gates :=
      ShiExplicitCirc.toffGates w₁ w₂ s h₁₂ h₁s h₂s
        ++ ShiExplicitCirc.toffGates w₂ w₃ s h₂₃ h₂s h₃s
        ++ ShiExplicitCirc.toffGates w₁ w₃ s h₁₃ h₁s h₃s
    ShiBQP.encCirc
        (ShiExplicitCirc.readCirc w₁ w₂ w₃ s h₁₂ h₁₃ h₂₃ h₁s h₂s h₃s)
      = ShiBQP.encNat 111 ++ (gates.map encGateLayer).flatten := by
  dsimp only
  unfold ShiExplicitCirc.readCirc ShiExplicitCirc.toffCirc
  rw [← List.map_append, ← List.map_append, encCirc_singleton_layers]
  rw [readout_gate_list_length]

end ShiTMExplicitBlocks
